module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.FiberFinrank

/-!
# Scheme-theoretic elliptic curves

This file owns the geometric elliptic-curve package `(E, f, 0)` over a scheme, together
with morphisms of elliptic curves over a base map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.EllipticCurve

variable {S T : Scheme.{u}}

/-- A morphism `E ⟶ S` equipped with a section `0 : S ⟶ E` is an elliptic curve over `S`
when it is proper and smooth of relative dimension one, and every fibre is a connected
genus-one curve in the sense that `H⁰` and `H¹` of the structure sheaf are one-dimensional. -/
class IsEllipticCurve (E : Over S) (zero : S ⟶ E.left) : Prop extends
    IsProper E.hom, SmoothOfRelativeDimension 1 E.hom where
  /-- The marked point is a section of the structure morphism. -/
  isSection : zero ≫ E.hom = 𝟙 S
  /-- The structure sheaf of every fibre has one-dimensional global sections. -/
  fiberH0 : ∀ s : S,
    Scheme.Hom.fiberCohomologyFinrank E.hom
      (SheafOfModules.unit E.left.ringCatSheaf : E.left.Modules) 0 s = 1
  /-- The structure sheaf of every fibre has one-dimensional first cohomology. -/
  fiberH1 : ∀ s : S,
    Scheme.Hom.fiberCohomologyFinrank E.hom
      (SheafOfModules.unit E.left.ringCatSheaf : E.left.Modules) 1 s = 1

namespace IsEllipticCurve

/-- An elliptic curve over `S` is proper, smooth of relative dimension one, equipped with a
section, and has `H⁰ = H¹ = 1` on every fibre of the structure sheaf. -/
theorem spec (E : Over S) (zero : S ⟶ E.left) [IsEllipticCurve E zero] :
    zero ≫ E.hom = 𝟙 S ∧
      IsProper E.hom ∧ SmoothOfRelativeDimension 1 E.hom ∧
      (∀ s : S,
        Scheme.Hom.fiberCohomologyFinrank E.hom
          (SheafOfModules.unit E.left.ringCatSheaf : E.left.Modules) 0 s = 1) ∧
      ∀ s : S,
        Scheme.Hom.fiberCohomologyFinrank E.hom
          (SheafOfModules.unit E.left.ringCatSheaf : E.left.Modules) 1 s = 1 := sorry

/-- The characterizing conditions for an elliptic curve over a scheme. -/
theorem iff (E : Over S) (zero : S ⟶ E.left) :
    IsEllipticCurve E zero ↔
      zero ≫ E.hom = 𝟙 S ∧
        IsProper E.hom ∧ SmoothOfRelativeDimension 1 E.hom ∧
        (∀ s : S,
          Scheme.Hom.fiberCohomologyFinrank E.hom
            (SheafOfModules.unit E.left.ringCatSheaf : E.left.Modules) 0 s = 1) ∧
        ∀ s : S,
          Scheme.Hom.fiberCohomologyFinrank E.hom
            (SheafOfModules.unit E.left.ringCatSheaf : E.left.Modules) 1 s = 1 := sorry

end IsEllipticCurve


/-- The zero section of the base change `a* E`, obtained by lifting `(a ≫ 0, 𝟙 T)`. -/
def pullbackSection (E : Over S) (zero : S ⟶ E.left) (a : T ⟶ S)
    (hzero : zero ≫ E.hom = 𝟙 S) :
    T ⟶ pullback E.hom a :=
  pullback.lift (a ≫ zero) (𝟙 T)
    (((Category.assoc a zero E.hom).trans (congrArg (fun f => a ≫ f) hzero)).trans
      ((Category.comp_id a).trans (Category.id_comp a).symm))

/-- The lifted zero section projects to the identity on the test scheme. -/
theorem pullbackSection_snd (E : Over S) (zero : S ⟶ E.left) (a : T ⟶ S)
    (hzero : zero ≫ E.hom = 𝟙 S) :
    pullbackSection E zero a hzero ≫ pullback.snd E.hom a = 𝟙 T :=
  pullback.lift_snd _ _ _

/-- The lifted zero section composes with the projection to `E` as `a ≫ 0`. -/
theorem pullbackSection_fst (E : Over S) (zero : S ⟶ E.left) (a : T ⟶ S)
    (hzero : zero ≫ E.hom = 𝟙 S) :
    pullbackSection E zero a hzero ≫ pullback.fst E.hom a = a ≫ zero :=
  pullback.lift_fst _ _ _

/-- Base change of an elliptic curve along a morphism of schemes remains an elliptic curve,
with zero section `pullbackSection`. -/
instance instIsEllipticCurve_pullback (E : Over S) (zero : S ⟶ E.left)
    [IsEllipticCurve E zero] (a : T ⟶ S) :
    IsEllipticCurve (Over.mk (pullback.snd E.hom a))
      (pullbackSection E zero a IsEllipticCurve.isSection) := sorry

variable {S' : Scheme.{u}}

/-- A morphism of elliptic curves over `a : S ⟶ S'` is a map on total spaces making a
cartesian square with `a` and sending the zero section of `E` to the zero section of `E'`. -/
structure HomOver (a : S ⟶ S') (E : Over S) (zero : S ⟶ E.left)
    (E' : Over S') (zero' : S' ⟶ E'.left) : Type u where
  /-- The underlying morphism of total spaces. -/
  hom : E.left ⟶ E'.left
  /-- The square formed with the structure morphisms and `a` is cartesian. -/
  isPullback : IsPullback hom E.hom E'.hom a
  /-- The morphism sends the zero section of `E` to the zero section of `E'`. -/
  comm_zero : zero ≫ hom = a ≫ zero'

namespace HomOver

/-- A morphism of elliptic curves over `a` is cartesian on total spaces and preserves zeros. -/
theorem spec {a : S ⟶ S'} {E : Over S} {zero : S ⟶ E.left}
    {E' : Over S'} {zero' : S' ⟶ E'.left} (φ : HomOver a E zero E' zero') :
    IsPullback φ.hom E.hom E'.hom a ∧ zero ≫ φ.hom = a ≫ zero' := sorry


/-- The identity morphism of an elliptic curve over itself. -/
def id (E : Over S) (zero : S ⟶ E.left) : HomOver (𝟙 S) E zero E zero where
  hom := 𝟙 E.left
  isPullback := IsPullback.id_horiz E.hom
  comm_zero := (Category.comp_id zero).trans (Category.id_comp zero).symm

end HomOver

end AlgebraicGeometry.EllipticCurve
