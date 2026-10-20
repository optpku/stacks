module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper.OpennessOfVersality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids

universe u

/- Lemma 99.13.9
The stack of finite-presentation, flat, proper algebraic spaces satisfies openness
of versality over every Noetherian base scheme, and in particular over Spec ℤ.
-/
@[stacks 0D3X] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.opennessOfVersality :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {U : Scheme.{u}}
    (hU : U ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType hU] (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U),
    IsFiniteTypePoint u0 → IsVersalAt hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.opennessOfVersality_specZ :
    ∀ {U : Scheme.{u}} (hU : U ⟶ specZ)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : FpFlatProperGroupoids specZ)
    (hx : (pFpFlatProperGroupoids specZ).obj x = Over.mk hU) (u0 : U),
    IsFiniteTypePoint u0 → IsVersalAt hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u)
