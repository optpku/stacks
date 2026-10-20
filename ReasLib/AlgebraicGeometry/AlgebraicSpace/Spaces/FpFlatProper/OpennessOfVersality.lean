module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper.Versal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Affine
public import ReasLib.RingTheory.Noetherian.ULift

/-!
# Openness of versality for finite-presentation, flat, proper algebraic spaces

Versality of a family over a Noetherian base spreads from a finite type point
to the finite type points of an open neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids

/-- A finite-presentation, flat, proper family over a scheme locally of finite
type over a Noetherian base is versal at every finite type point of some open
neighbourhood of any finite type point at which it is versal. -/
theorem opennessOfVersality {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {U : Scheme.{u}}
    (hU : U ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType hU] (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U) :
    IsFiniteTypePoint u0 → IsVersalAt hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u :=
  sorry


/-- A finite-presentation, flat, proper family over a scheme locally of finite
type over `specZ` is versal at every finite type point of some open neighbourhood
of any finite type point at which it is versal. -/
theorem opennessOfVersality_specZ {U : Scheme.{u}} (hU : U ⟶ specZ)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : FpFlatProperGroupoids specZ)
    (hx : (pFpFlatProperGroupoids specZ).obj x = Over.mk hU) (u0 : U) :
    IsFiniteTypePoint u0 → IsVersalAt hU x hx u0 →
      ∃ U' : Opens U, u0 ∈ U' ∧
        ∀ u : U, u ∈ U' → IsFiniteTypePoint u → IsVersalAt hU x hx u :=
  opennessOfVersality hU x hx u0

end AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids
