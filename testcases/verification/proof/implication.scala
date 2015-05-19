package test

import leon.lang._
import leon.proof._

object ImplicationExample {
    /*
     * Some implication example.
     *
     * This example actually is based on incorrect premises but
     * the proof in itself should correct.
     */

    sealed abstract class LegsProposition
    case object HasEigthLegs extends LegsProposition
    case object DoesntHaveEigthLegs extends LegsProposition

    implicit def boolean2Legs(prop: Boolean) = if (prop) HasEigthLegs else DoesntHaveEigthLegs
    implicit def legs2boolean(prop: LegsProposition) = prop match {
        case HasEigthLegs => true
        case _ => false
    }

    sealed abstract class PokerPlayerProposition
    case object IsPokerPlayer extends PokerPlayerProposition
    case object NoPokerPlayer extends PokerPlayerProposition

    // NB: no implicit conversions!
    def pokerPlayer2boolean(prop: PokerPlayerProposition): Boolean = prop match {
        case IsPokerPlayer => true
        case _ => false
    }

    sealed abstract class Animal
    case class Insect() extends Animal
    case class Mamal() extends Animal

    def insectsHaveEightLegs: Boolean = {
        true // That's a "fact".
    }.holds

    def mamalHaveEigthLegs: Boolean = {
        false // Another fact.
    }.fallacy

    def hasEigthLegs(a: Animal): LegsProposition = a match {
        case Insect() => insectsHaveEightLegs
        case Mamal() => mamalHaveEigthLegs
    }

    val jeff = Insect()

    def jeffIsAnInsect: Boolean = (jeff match {
        case Insect() => true
        case _ => false
    }).holds // Yet another fact.

    def isAnInsect(a: Animal): Boolean = a match {
        case Insect() => true
        case _ => false
    }

    def isJeff(a: Animal) = jeff == a

    def jeffHasEigthLegs: Boolean = {
        insectsHaveEightLegs because isAnInsect(jeff)
    }.holds

    def animalsWithEigthLegsPlayPoker: Boolean = {
        true // Some other facts
    }.holds

    def animalsWithoutEigthLegsDontPlayPoker: Boolean = {
        false // Idem
    }.fallacy

    def isAPokerPlayer(prop: LegsProposition): PokerPlayerProposition = prop match {
        case HasEigthLegs => IsPokerPlayer
        case _ => NoPokerPlayer
    }//.ensuring{ res => (res == IsPokerPlayer) == (prop == HasEigthLegs) }

    // Jeff has 8 legs
    def lemma1(a: Animal): Boolean = {
        (isJeff(a) implies isAnInsect(jeff)) implies hasEigthLegs(jeff) // because insect have 8 legs
    }.holds

    // Jeff plays Poker
    def lemma2(a: Animal): Boolean = {
        {
            // false implies
            isJeff(a)                       ==>| trivially                |
            isAnInsect(jeff)                ==>| trivially                |
            insectsHaveEightLegs            ==>| trivially                |
            isAPokerPlayer(HasEigthLegs)    ==>| pokerPlayer2boolean        // no implicit convertion
        }.qed
    }.holds

    // Not all poker player are Jeff...
    def fallacy1(a: Animal): Boolean = {
        {
            isAPokerPlayer(HasEigthLegs) ==>| pokerPlayer2boolean |
            insectsHaveEightLegs         ==>| trivially           |
            isAnInsect(jeff)             ==>| trivially           |
            isJeff(a)                    ==>| trivially
        }.qed
    }.holds
}

// vim: set ts=4 sw=4 et:
