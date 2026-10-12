/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint

/-!
# Points of the small pro-étale site

A geometric point of `S` determines a point of the small pro-étale site `S.ProEt`,
whose fibre is the coyoneda fibre of the structure morphism. Stalks of
presheaves are the corresponding presheaf fibres.
-/

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {S : Scheme.{u}}

/-- The category of pro-étale neighbourhoods of a geometric point, as the
category of elements of the coyoneda fibre of its structure morphism on
`S.ProEt`. -/
abbrev ProetaleNeighborhood (s : GeometricPoint S) :=
  (ProEt.forget S ⋙ coyoneda.obj (op (Over.mk s.hom))).Elements

namespace ProetaleNeighborhood

/-- The object of the small pro-étale site underlying a pro-étale neighbourhood. -/
abbrev toProEt {s : GeometricPoint S} (U : ProetaleNeighborhood s) : S.ProEt :=
  U.1

/-- The chosen lift of a geometric point to a pro-étale neighbourhood. -/
abbrev lift {s : GeometricPoint S} (U : ProetaleNeighborhood s) :
    Spec (.of s.K) ⟶ U.toProEt.left :=
  U.2.left

/-- The chosen lift of a geometric point commutes with the pro-étale structure morphism. -/
theorem lift_fac {s : GeometricPoint S} (U : ProetaleNeighborhood s) :
    U.lift ≫ U.toProEt.hom = s.hom :=
  sorry

/-- Construct a pro-étale neighbourhood from a weakly étale scheme over `S` and a
lift of the geometric point. -/
def of {s : GeometricPoint S} (U : S.ProEt)
    (u : Spec (.of s.K) ⟶ U.left) (hu : u ≫ U.hom = s.hom) :
    ProetaleNeighborhood s :=
  Functor.elementsMk _ U (Over.homMk u hu)

/-- The chosen lift of the neighbourhood constructed by `of` is the supplied lift. -/
theorem of_lift {s : GeometricPoint S} (U : S.ProEt)
    (u : Spec (.of s.K) ⟶ U.left) (hu : u ≫ U.hom = s.hom) :
    (of U u hu).lift = u :=
  sorry

/-- A morphism of pro-étale neighbourhoods is a morphism in the category of
elements, hence an `S`-morphism preserving the chosen lifts. -/
abbrev Hom {s : GeometricPoint S} (V U : ProetaleNeighborhood s) :=
  V ⟶ U

namespace Hom

/-- The pro-étale morphism underlying a morphism of pro-étale neighbourhoods. -/
abbrev toProEtHom {s : GeometricPoint S} {V U : ProetaleNeighborhood s}
    (f : Hom V U) : V.toProEt ⟶ U.toProEt :=
  f.val

/-- The scheme morphism underlying a morphism of pro-étale neighbourhoods. -/
abbrev schemeHom {s : GeometricPoint S} {V U : ProetaleNeighborhood s}
    (f : Hom V U) : V.toProEt.left ⟶ U.toProEt.left :=
  f.toProEtHom.left

/-- A morphism of pro-étale neighbourhoods preserves the selected lifts. -/
theorem lift_fac {s : GeometricPoint S} {V U : ProetaleNeighborhood s}
    (f : Hom V U) : V.lift ≫ f.schemeHom = U.lift :=
  sorry

/-- The underlying scheme map of a morphism of pro-étale neighbourhoods is an `S`-morphism. -/
theorem over_fac {s : GeometricPoint S} {V U : ProetaleNeighborhood s}
    (f : Hom V U) : f.schemeHom ≫ U.toProEt.hom = V.toProEt.hom :=
  sorry

/-- Construct a morphism of pro-étale neighbourhoods from a pro-étale morphism
preserving the selected lifts. -/
def of {s : GeometricPoint S} {V U : ProetaleNeighborhood s}
    (f : V.toProEt ⟶ U.toProEt) (hf : V.lift ≫ f.left = U.lift) : Hom V U :=
  CategoryOfElements.homMk V U f sorry

/-- The underlying scheme map of the neighbourhood morphism constructed by `of`
is the supplied pro-étale morphism. -/
theorem of_schemeHom {s : GeometricPoint S} {V U : ProetaleNeighborhood s}
    (f : V.toProEt ⟶ U.toProEt) (hf : V.lift ≫ f.left = U.lift) :
    (of f hf).schemeHom = f.left :=
  sorry

end Hom

end ProetaleNeighborhood

/-- A geometric point `s` of `S` determines a point of the small pro-étale site
`S.ProEt`, whose fibre functor sends a weakly étale `U` to the set of lifts of
`s` through `U`. -/
def toSmallProetalePoint (s : GeometricPoint S) : (ProEt.topology S).Point where
  fiber := ProEt.forget S ⋙ coyoneda.obj (op (Over.mk s.hom))
  isCofiltered := sorry
  initiallySmall := sorry
  jointly_surjective := sorry

/-- The fibre functor of `toSmallProetalePoint s` is the coyoneda fibre of `s.hom`
on the small pro-étale site. -/
theorem toSmallProetalePoint_fiber (s : GeometricPoint S) :
    (toSmallProetalePoint s).fiber =
      ProEt.forget S ⋙ coyoneda.obj (op (Over.mk s.hom)) :=
  sorry

end AlgebraicGeometry.Scheme.GeometricPoint

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}}

/-- The stalk of a presheaf on the small pro-étale site at a geometric point is
the presheaf fibre of the associated site point, i.e. the colimit over pointed
pro-étale neighbourhoods. -/
abbrev stalk (s : GeometricPoint S) (F : S.ProEtᵒᵖ ⥤ Type u) : Type u :=
  (GeometricPoint.toSmallProetalePoint s).presheafFiber.obj F

/-- The pro-étale stalk is definitionally the presheaf fibre of the associated
small pro-étale point. -/
theorem stalk_def (s : GeometricPoint S) (F : S.ProEtᵒᵖ ⥤ Type u) :
    stalk s F = (GeometricPoint.toSmallProetalePoint s).presheafFiber.obj F :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
