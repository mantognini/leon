.. _verification:

Verification
============

Software verification aims at making software safer. In its typical use case,
it is a tool that takes as input the source code of a program with
specifications as annotations and attempt to prove --- or disprove --- their
validity.

One of the core module of Leon is a verifier for the subset of Scala described
in the sections :ref:`Pure Scala <purescala>` and :ref:`XLang <xlang>`. In this
section we describe the specification language that can be used to declare
properties of programs, as well as the safety properties automatically checked
by Leon. We also discuss how Leon can be used to prove mathematical theorems.

Verification conditions
-----------------------

Given an input program, Leon generates individual verification conditions
corresponding to different properties of the program. A program is correct if
all of the generated verification conditions are ``valid``. The validity of some
conditions depends on the validity of other conditions --- typically a
postcondition is ``valid`` assuming the precondition is ``valid``.

For each function, Leon attempts to verify its contract, if there is one. A
*contract* is the combination of a *precondition* and a *postcondition*. A
function meets its contract if for any input parameter that passes the
precondition, the postcondition holds after executing the function.
Preconditions and postconditions are annotations given by the user --- they are
the specifications and hence cannot be inferred by a tool and must be provided.

In addition to user-provided contracts, Leon will also generate a few safety
verification conditions of its own. It will check that all of the array
accesses are within proper bounds, and that pattern matching always covers all
possible cases, even given complex precondition. The latter is different from
the Scala compiler checks on pattern matching exhaustiveness, as Leon considers
information provided by (explicit or implicit) preconditions to the ``match``
expression.

Postconditions
**************

One core concept in verification is to check the contract of functions. The most
important part in a contract is the postcondition. The postcondition specifies
the behaviour of the function. It takes into account the precondition and only
asserts the property of the output when the input satisfies the precondition.

Formally, we consider a function with a single parameter (one can generalize
the following for any number of parameters):

.. code-block:: scala

   def f(x: A): B = {
     require(prec)
     body
   } ensuring(r => post)

where, :math:`\mbox{prec}(x)` is a boolean expression with free variables
contained in :math:`\{ x \}`, :math:`\mbox{body}(x)` is a boolean expression with
free variables contained in :math:`\{ x \}` and :math:`\mbox{post}(x, r)` is a
boolean expression with free variables contained in :math:`\{ x, r \}`. The
types of :math:`x` and :math:`r` are respectively ``A`` and ``B``. We write
:math:`\mbox{expr}(a)` to mean the substitution in :math:`\mbox{expr}` of its
free variable by :math:`a`.

Leon attempts to prove the following theorem:

.. math::

  \forall x. \mbox{prec}(x) \implies \mbox{post}(x, \mbox{body}(x))

If Leon is able to prove the above theorem, it returns ``valid`` for the
function ``f``. This gives you a guarantee that the function ``f`` is correct
with respect to its contract.

However, if the theorem is not valid, Leon will return a counterexample to the
theorem. The negation of the theorem is:

.. math::

  \exists x. \mbox{prec}(x) \land \neg \mbox{post}(x, \mbox{body}(x))

and to prove the validity of the negation, Leon finds a witness :math:`x` --- a
counterexample --- such that the precondition is verified and the postcondition
is not.

The general problem of verification is undecidable for a Turing-complete
language, and the Leon language is Turing-complete. So Leon has to be
incomplete in some sense. Generally, Leon will eventually find a counterexample
if one exists. However, in practice some program structures require too many
unrollings and Leon is likely to timeout (or being out of memory) before
finding the counterexample.  When the postcondition is valid, it could also
happen that Leon keeps unrolling the program forever, without being able to
prove the correctness. We discuss the exact conditions for this in the
chapter on Leon's algorithms.

Preconditions
*************

Preconditions are used as part of the contract of functions. They are a way to
restrict the input to only relevant inputs, without having to implement guards
and error handling in the functions themselves.

Preconditions are contracts that the call sites should respect, and thus are
not checked as part of verifying the function. Given the following definition:

.. code-block:: scala

   def f(x: A): B = {
     require(prec)
     body
   }


For each call site in the whole program (including in ``f`` itself):

.. code-block:: scala

   ...
   f(e)
   ...

where the expression :math:`\mbox{e}(x)` is an expression of type ``A`` with
free variables among :math:`\{ x \}`. Let us define the path condition on :math:`x`
at that program point as :math:`\mbox{pc}(x)`. The path condition is a formula that
summarizes the facts known about :math:`x` at that call site. A typical example is
when the call site is inside an if expression:

.. code-block:: scala

   if(x > 0)
     f(x)

The path condition on :math:`x` would include the fact that :math:`x > 0`. This
path condition is then used as a precondition of proving the validity of the
call to :math:`\mbox{f}`. Formally, for each such call site, Leon will attempt
to prove the following theorem:

.. math::

   \forall x. \mbox{pc}(x) \implies \mbox{prec}(\mbox{e}(x))

Leon will generates one such theorem for each static call site of a function with
a precondition.

.. note::

   Leon only assumes an open program model, where any function could be called from
   outside of the given program. In particular, Leon will not derive a precondition
   to a function based on known information in the context of the calls, such as
   knowing that the function is always given positive parameters. Any information needed
   to prove the postcondition will have to be provide as part of the precondition
   of a function.

Loop invariants
***************

Leon supports annotations for loop invariants in :ref:`XLang <xlang>`. To
simplify the presentation we will assume a single variable :math:`x` is in
scope, but the definitions generalize to any number of variables. Given the
following program:

.. code-block:: scala

   (while(cond) {
     body
   }) invariant(inv)

where the boolean expression :math:`\mbox{cond}(x)` is over the free variable
:math:`x` and the expression :math:`\mbox{body}(x, x')` relates the value of
:math:`x` when entering the loop to its updated value :math:`x'` on loop exit.
The expression :math:`\mbox{inv}(x)` is a boolean formula over the free
variable :math:`x`.

A loop invariant must hold:
  (1) when the program enters the loop initially
  (2) after each completion of the body
  (3) right after exiting the loop (when the condition turns false)

Leon will prove point (1) and (2) above. Together, and by induction, they imply
that point (3) holds as well.

Array access safety
*******************

Leon generates verification conditions for the safety of array accesses. For
each array variable, Leon carries along a symbolic information on its length.
This information is used to prove that each expression used as an index in the
array is strictly smaller than that length. The expression is also checked to
be positive.

Pattern matching exhaustiveness
*******************************

Leon verifies that pattern matching is exhaustive. The regular Scala compiler
only considers the types of expression involved in pattern matching, but Leon
will consider information such as precondition to formally prove the
exhaustiveness of pattern matching.

As an example, the following code should issue a warning with Scala:

.. code-block:: scala

   abstract class List
   case class Cons(head: Int, tail: List) extends List
   case object Nil extends List

   def getHead(l: List): Int = {
     require(!l.isInstanceOf[Nil])
     l match {
       case Cons(x, _) => x
     }
   }

But Leon will actually prove that the pattern matching is actually exhaustive,
relying on the given precondition.

Proving mathematical theorems with Leon
---------------------------------------

As we have seen, verifying the contract of a function is really proving a mathematical
theorem. In some sense, Leon can be seen as a (mostly) automated theorem prover. It is
automated in the sense that once the property stated, Leon will proceed with searching
for a proof without any user interaction. In practice however, many theorems will be fairly
difficult to prove, and it is possible for the user to provide hints to Leon.

Hints typically take the form of simpler properties that combine in order to prove
more complicated ones.

Neon
====

.. TODO decide how previous § & what follows should be integrated together (or
   not)

A practical introduction to proofs
----------------------------------

When writing preconditions or postconditions, one is basically writing boolean
propositions. It can be as simple as testing whether a list is empty or not, to
more complex combinations of properties.  Lemmas or theorems can then be
expressed using boolean-valued methods to ensure they are tautologies, or, in
other words, that their statement holds for all valid inputs.

To make this more concrete, let's take a simple lemma as an example. Here we
want to prove that the append operation (``++``) on list preserves the content
of the two lists being concatenated. The proof is relatively straightforward and
Leon succeeds to prove the lemma always holds.

.. code-block:: scala

    import leon.collection._ // for List
    import leon.lang._       // for holds

    object Example {
      def appendContent[A](l1: List[A], l2: List[A]): Boolean = {
        l1.content ++ l2.content == (l1 ++ l2).content
      }.holds
    }

.. NOTE I used appendContent instead of appendAssoc because the latter use
   @induct

Here we wrote ``.holds`` which is a method implicitly available on ``Boolean``
that ensure the returned value is ``true``. It is equivalent to writing
``ensuring { res => res }``, or, more concisely, ``ensuring{_}``.

Now let's look at another example that looks trivial but for which Leon
actually needs some help for the proof: we want to prove that adding ``Nil``
at the end of a list has no effect.

.. code-block:: scala

    import leon.collection._ // for List
    import leon.lang._       // for holds

    object Example {
      def rightUnitAppend[T](l1: List[T]): Boolean = {
        l1 ++ Nil() == l1
      }.holds
    }

If you try to verify this last example you'll face a delicate situation: Leon
runs indeterminately until it is either killed or timeout. But why does this
happen?  The statement doesn't seems more complicated than with
``appendContent``...

.. TODO would it be better to move the next paragraph in §General idea?

The problem is that, in the implementation of ``++``, the recursion is on the
first parameter (here ``l1``). So we need to augment the proof with a recursion
on ``l1`` to palliate to this issue and give a complete explanation to Leon as
of why adding ``Nil`` to the left of a list has no effect.

.. code-block:: scala

    import leon.collection._ // for List
    import leon.lang._       // for holds
    import leon.proof._      // for because

    object Example {
      def rightUnitAppend[T](l1: List[T]): Boolean = {
        (l1 ++ Nil() == l1) because {
          l1 match {
            case Nil()       => true
            case Cons(x, xs) => rightUnitAppend(xs)
          }
        }
      }.holds
    }

With this new implementation of the ``rightUnitAppend`` lemma, Leon is capable
of verifying it holds. If you look closely at it, you can distinguish three
parts:

1. the claim we want to prove ``l1 ++ Nil() == l1``;
2. ``because``, which is just some syntactic sugar for conjunction -- remember,
   every proposition is a Boolean formula;
3. and some recursion on ``l1`` that serves as a hint for Leon.

The recursion is based here on pattern matching, which Leon will also check for
exhaustiveness, that has essentially the same structure as the one present in
the implementation of ``++``: the base case is when ``l1`` is the empty string
and the inductive case is performed on ``Cons`` objects.

.. TODO add the same example but with @induct

General idea
************

.. TODO explain because (if more need to be said) and check

.. TODO sketch limitations

Induction
*********

.. TODO natural + natural induction

.. TODO @induct / case analysis

.. TODO examples: rightUnitAppend with induct

Relational reasoning
********************

Since many theorems have proofs involving relational reasoning, it is good to
know how their properties (such as transitivity, reflexivity or symmetry) work
in Leon, when one can rely on them to build proof or instead needs to give
hints.

When working with simple structural equality, we can rely on the default ``==``
operator and Leon will happily understand when the reflexivity, symmetry and
transitivity properties apply and use them to conclude bigger proofs. Similarly,
when working on ``BigInt``, it knows about reflexivity, antisymmetry and
transitivity over ``>=`` or ``<=`` , and also the antireflexivity, antisymmetry
and transitivity of ``>`` and ``<``.

However, even for relatively simple proofs Leon needs more information about
other operations, such as appending a list to another one, in order to use
those relations. For example, when proving that, for two lists ``l1`` and
``l2``, the following statement holds, Leon will not be able to find a witness.

.. code-block:: scala

    (l1 ++ l2).reverse == l2.reverse ++ l1.reverse

The hard part of giving hints to Leon is actually finding them. Here we can
apply a general principle on top of classic structural induction: we start from
the left hand side of the statement and build, with equality, a path to the
right hand side. Using ``check`` statement we can identify where Leon timeouts
and therefore focus on where it does need hints.

.. code-block:: scala

    def reverseAppend[T](l1: List[T], l2: List[T]): Boolean = {
      ( (l1 ++ l2).reverse == l2.reverse ++ l1.reverse ) because {
        l1 match {
          case Nil() =>
            /* 1 */ check { (Nil() ++ l2).reverse == l2.reverse                  } &&
            /* 2 */ check { l2.reverse            == l2.reverse ++ Nil()         } &&
            /* 3 */ check { l2.reverse ++ Nil()   == l2.reverse ++ Nil().reverse }
          case Cons(x, xs) =>
            /* 4 */ check { ((x :: xs) ++ l2).reverse       == (x :: (xs ++ l2)).reverse       } &&
            /* 5 */ check { (x :: (xs ++ l2)).reverse       == (xs ++ l2).reverse :+ x         } &&
            /* 6 */ check { (xs ++ l2).reverse :+ x         == (l2.reverse ++ xs.reverse) :+ x } &&
            /* 7 */ check { (l2.reverse ++ xs.reverse) :+ x == l2.reverse ++ (xs.reverse :+ x) } &&
            /* 8 */ check { l2.reverse ++ (xs.reverse :+ x) == l2.reverse ++ (x :: xs).reverse }
        }
      }
    }.holds

If you run the above code with a decent timeout, Leon should give you four
*UNKNOWN*: the postcondition of the ``reverseAppend`` function itself and
checks number 2, 6 and 7.

Check #2 fails because, as we saw earlier, Leon is not capable of guessing the
``rightUnitAppend`` lemma by itself. To palliate to this shortcoming we just
need to instantiate this lemma by adding ``&& rightUnitAppend(l2.reverse)`` to
the base case.

Check #6 fails because, at this point, we need to inject the induction
hypothesis on ``xs`` and ``l2`` by adding ``&& reverseAppend(xs, l2)``.

Finally, check #7 fails for a similar raison to #2: we need an external lemma
to prove that ``(l1 ++ l2) :+ t == l1 ++ (l2 :+ t)`` holds for any ``l1``,
``l2`` and ``t``. We call this lemma ``snocAfterAppend`` and leave it as an
exercise for the reader.

So now that we have a valid proof for Leon, we can try to optimise it for
readability. Indeed, the resulting code is all but DRY: every sides of
equalities are repeated twice to connect them. We could either remove all the
unnecessary code for the proof and only write:

.. code-block:: scala

     def reverseAppend[T](l1: List[T], l2: List[T]): Boolean = {
       ( (l1 ++ l2).reverse == l2.reverse ++ l1.reverse ) because {
         l1 match {
           case Nil() =>
             rightUnitAppend(l2.reverse)
           case Cons(x, xs) =>
             reverseAppend(xs, l2) && snocAfterAppend(l2.reverse, xs.reverse, x)
         }
       }
     }.holds

Or we can use some proof DSL to embed hints in the reasonings themselves and
not lose information that is still useful for human being reading the proof
later on:

.. code-block:: scala

    def reverseAppend[T](l1: List[T], l2: List[T]): Boolean = {
      ( (l1 ++ l2).reverse == l2.reverse ++ l1.reverse ) because {
        l1 match {
          case Nil() => {
            (Nil() ++ l2).reverse         ==| trivial                     |
            l2.reverse                    ==| rightUnitAppend(l2.reverse) |
            l2.reverse ++ Nil()           ==| trivial                     |
            l2.reverse ++ Nil().reverse
          }.qed
          case Cons(x, xs) => {
            ((x :: xs) ++ l2).reverse         ==| trivial               |
            (x :: (xs ++ l2)).reverse         ==| trivial               |
            (xs ++ l2).reverse :+ x           ==| reverseAppend(xs, l2) |
            (l2.reverse ++ xs.reverse) :+ x   ==|
              snocAfterAppend(l2.reverse, xs.reverse, x)                |
            l2.reverse ++ (xs.reverse :+ x)   ==| trivial               |
            l2.reverse ++ (x :: xs).reverse
          }.qed
        }
      }
    }.holds

As you can see in the above code, the idea is to group statements in a block
(``{ }``) and call ``qed`` on it. Then, instead of writing ``a == b && b == c
&& hint1 && hint2`` we write ``a ==| hint1 | b ==| hint2 | c``. And when no
additional hint is required, we can use ``trivial`` which simply stands for
``true``.

Additionally, by using this DSL, we get the same feedback granularity from Leon
as if we had used ``check`` statements. This way we can construct proofs based
on equality more easily and directly identify where hints are vital.

.. TODO limitations of DSL

Limits of the approach: HOF & quantifiers
*****************************************

.. TODO example: folds + future work (alt. version of folds)

Technique for proving non-trivial post-conditions
-------------------------------------------------

.. TODO example: Meas.apply(xs) (+ def of Empty/Cons)

A complex example: additivity of measures
-----------------------------------------

.. TODO

Recap
-----

.. TODO lessons learned


