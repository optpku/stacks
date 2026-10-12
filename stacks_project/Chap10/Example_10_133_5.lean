/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.FirstOrder
public import ReasLib.Algebra.Module.PrincipalParts.FirstOrder.Decomposition
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.133.5

@stack 09CM

Example 10.133.5 (Tag 09CM): for a commutative `R`-algebra `S`, a first-order
differential operator `S → N` is canonically a derivation plus its value at `1`.
Using Kähler differentials, this is a cotangent-map plus a value; specializing the
principal-parts representation gives `PrincipalParts.module R S S 1 ≃ Ω[S⁄R] × S`.

The reusable owners are `DifferentialOperator.FirstOrder` for the operator
splittings and `PrincipalParts.FirstOrder` for the represented first-principal-
parts splitting.  This chapter file deliberately records the source statements
without retaining a second, chapter-local implementation of their maps.
-/

@[stacks 09CM]
#check @DifferentialOperator.FirstOrder.equivDerivationProd

#check @DifferentialOperator.FirstOrder.equivCotangentProd
#check @DifferentialOperator.FirstOrder.equivCotangentProd_natural
#check @PrincipalParts.FirstOrder.representingEquivCotangentProd
#check @PrincipalParts.FirstOrder.representingEquivCotangentProd_natural
#check @PrincipalParts.FirstOrder.equivCotangentProd
