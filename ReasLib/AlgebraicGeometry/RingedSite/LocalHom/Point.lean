module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged.Point
public import ReasLib.AlgebraicGeometry.RingedSite.LocalHom
public import ReasLib.AlgebraicGeometry.RingedSite.Stalk
import Mathlib.Tactic.CrossRefAttribute

/-!
# Point criteria for local morphisms of commutative ringed sites

The canonical map on stalk rings is owned by the bundled ringed-site morphism.  Locality can be
tested on these maps when the source site has enough points, or on any conservative family of
points.  This keeps point transport and the inverse-image comparison out of downstream APIs.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace RingedSite.Hom

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪C : Sheaf JC CommRingCat.{max u v}}
variable {𝒪D : Sheaf JD CommRingCat.{max u v}}
variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪C)
  (RingedSite.ofCommRingSheaf JD 𝒪D))
variable [(f.base.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]

/-- A local morphism induces a local homomorphism on every
commutative-ring stalk. -/
@[stacks 04H9 "(1)"]
instance stalkMap_isLocalHom [f.IsLocal]
    (p : GrothendieckTopology.Point.{max u v} JC)
    [InitiallySmall (f.base ⋙ p.fiber).Elements] :
    IsLocalHom (stalkMap f p).hom := sorry

/-- When the source site has enough points, locality of a bundled
ringed-site morphism is equivalent to locality of all its canonical stalk maps. -/
@[stacks 04H9 "(2)"]
theorem isLocal_iff_stalkMap_isLocalHom
    [GrothendieckTopology.HasEnoughPoints.{max u v} JC]
    [∀ p : GrothendieckTopology.Point.{max u v} JC,
      InitiallySmall (f.base ⋙ p.fiber).Elements] :
    f.IsLocal ↔
      ∀ p : GrothendieckTopology.Point.{max u v} JC,
        IsLocalHom (stalkMap f p).hom := sorry

/-- Between locally ringed presentations, locality of a stalk map is
equivalent to preservation of the distinguished maximal ideals. -/
@[stacks 04H9 "(3)"]
theorem stalkMap_isLocalHom_iff_comap_maximalIdeal
    [HasWeakSheafify JC (Type (max u v))]
    [JC.HasSheafCompose (forget CommRingCat.{max u v})]
    [HasWeakSheafify JD (Type (max u v))]
    [JD.HasSheafCompose (forget CommRingCat.{max u v})]
    [𝒪C.IsLocallyRinged] [𝒪D.IsLocallyRinged]
    (p : GrothendieckTopology.Point.{max u v} JC)
    [InitiallySmall (f.base ⋙ p.fiber).Elements] :
    IsLocalHom (stalkMap f p).hom ↔
      Ideal.comap (stalkMap f p).hom (IsLocalRing.maximalIdeal (p.stalkCommRing 𝒪C)) =
        IsLocalRing.maximalIdeal ((pointMap f p).stalkCommRing 𝒪D) := sorry

/-- Locality on a conservative family of source points implies
global locality of the bundled morphism. -/
@[stacks 04H9 "(4)"]
theorem IsLocal.of_stalkMap
    (P : ObjectProperty (GrothendieckTopology.Point.{max u v} JC))
    [∀ p : GrothendieckTopology.Point.{max u v} JC,
      InitiallySmall (f.base ⋙ p.fiber).Elements]
    (hP : P.IsConservativeFamilyOfPoints)
    (h : ∀ (p : GrothendieckTopology.Point.{max u v} JC),
      P p → IsLocalHom (stalkMap f p).hom) :
    f.IsLocal := sorry

end RingedSite.Hom
