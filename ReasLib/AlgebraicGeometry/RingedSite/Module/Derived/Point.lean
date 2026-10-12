/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Grp.Presheaf.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Constant.Chaotic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Underlying
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Evaluation
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Point
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived lower shriek to a point

This leaf owns the reusable projection-to-a-point functor for module sheaves.  The construction
first forgets module structure to additive presheaves and then applies the total derived colimit.
The point construction is independent of any chapter-specific presentation; chaotic and constant
ringed sites are supplied as thin specializations below.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape
open Opposite
open SheafOfModules.RingedSite
open RingedSite.Hom
open scoped CategoryTheory

noncomputable section

universe z u v w

namespace RingedSite.Hom.DerivedPoint

variable {C : Type u} [Category.{v} C]

section General

variable {X : RingedSite.{u, v, w}}

/-- The derived lower shriek of a ringed-site module category over the projection to a point.

The only site-specific input is exactness of the forgetful functor to additive presheaves.  This
keeps the point construction reusable for chaotic sites, ordinary sites with exact sheaf
forgetful functors, and later coefficient categories without duplicating a derived model.
-/
@[stacks 08RX "derived lower shriek to a point"]
noncomputable abbrev lowerShriek
    [UnivLE.{max u v, z}]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [PreservesFiniteColimits
      (sheafToPresheaf X.siteTopology AddCommGrpCat.{z})]
    [HasColimitsOfShape Xᵒᵖ AddCommGrpCat.{z}]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived X AddCommGrpCat.{z})
      (HomotopyCategory.quasiIso (Xᵒᵖ ⥤ AddCommGrpCat.{z}) (up ℤ))] :
    ModuleDerived.{z} X ⥤ DerivedCategory AddCommGrpCat.{z} :=
  underlyingAbelianPresheafDerived.{z} X ⋙
    categoryOverPointDerivedColimit X AddCommGrpCat.{z}

end General

namespace Chaotic

variable {O O' : Sheaf (⊥ : GrothendieckTopology C) RingCat.{w}}
variable [UnivLE.{max u v, w}]

/-- Derived extension of scalars on a chaotic site.  The topology is fixed at `⊥`, so the
construction is the canonical same-site ringed-site morphism rather than a site-parameterized
wrapper. -/
@[stacks 06YY "chaotic derived extension of scalars"]
noncomputable abbrev tensor (α : O ⟶ O') [UnivLE.{max u v, z}]
    [RingedSite.SameSite.HasPullbackDerived.{u, v, w, z} α] :
    ModuleDerived.{z} (RingedSite.ofRingSheaf (⊥ : GrothendieckTopology C) O) ⥤
      ModuleDerived.{z} (RingedSite.ofRingSheaf (⊥ : GrothendieckTopology C) O') :=
  RingedSite.SameSite.pullbackDerived.{u, v, w, z} α

/-- The map induced on the derived lower shriek of the unit by a chaotic structure-sheaf map. -/
@[stacks 08RX "chaotic lower-shriek unit comparison"]
noncomputable abbrev unitComparison (α : O ⟶ O')
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C AddCommGrpCat.{w})
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat.{w}) (up ℤ))] :=
  (lowerShriek
    (X := RingedSite.ofRingSheaf (⊥ : GrothendieckTopology C) O)).map
    ((DerivedCategory.singleFunctor (SheafOfModules O) (0 : ℤ)).map
      (SheafOfModules.unitToPushforwardObjUnit
        (RingedSite.SameSite.structureMap α)))

/-- The canonical isomorphism corresponding to `unitComparison`, when its invertibility is known. -/
@[stacks 08RX "chaotic lower-shriek unit comparison isomorphism"]
noncomputable abbrev unitComparisonIso (α : O ⟶ O')
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C AddCommGrpCat.{w})
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat.{w}) (up ℤ))]
    [IsIso (unitComparison α)] :=
  asIso (unitComparison α)

namespace tensor

/-- Lemma 21.39.12 (08RX), functor form: under the pointlike hypothesis and an invertible unit
comparison, derived extension of scalars does not change the point lower shriek. -/
@[stacks 08RX "chaotic derived lower-shriek change of rings"]
theorem lowerShriek_isomorphic
    (α : O ⟶ O')
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C AddCommGrpCat.{w})
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat.{w}) (up ℤ))]
    (hUbullet : ∃ Ubullet : CosimplicialObject C,
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    [RingedSite.SameSite.HasPullbackDerived.{u, v, w, w} α]
    [IsIso (unitComparison α)] :
    IsIsomorphic
      (lowerShriek
        (X := RingedSite.ofRingSheaf (⊥ : GrothendieckTopology C) O))
      (tensor α ⋙ lowerShriek
        (X := RingedSite.ofRingSheaf (⊥ : GrothendieckTopology C) O')) := sorry

/-- Objectwise form of `lowerShriek_isomorphic`, convenient for downstream calculations. -/
@[stacks 08RX "chaotic derived lower-shriek change of rings on objects"]
theorem lowerShriek_obj_isomorphic
    (α : O ⟶ O')
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C AddCommGrpCat.{w})
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat.{w}) (up ℤ))]
    (hUbullet : ∃ Ubullet : CosimplicialObject C,
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    [RingedSite.SameSite.HasPullbackDerived.{u, v, w, w} α]
    [IsIso (unitComparison α)]
    (K : ModuleDerived.{w} (RingedSite.ofRingSheaf (⊥ : GrothendieckTopology C) O)) :
    IsIsomorphic
      ((lowerShriek
        (X := RingedSite.ofRingSheaf (⊥ : GrothendieckTopology C) O)).obj K)
      ((lowerShriek
        (X := RingedSite.ofRingSheaf (⊥ : GrothendieckTopology C) O')).obj
        ((tensor α).obj K)) := sorry

end tensor

namespace Comm

variable {R R' : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{w}}

/-- The commutative-ring bridge for `Chaotic.tensor`; the reusable owner works at the underlying
`RingCat` layer, while this spelling preserves the source-facing commutative presentation. -/
@[stacks 06YY "commutative chaotic derived extension of scalars"]
noncomputable abbrev tensor (α : R ⟶ R') [UnivLE.{max u v, z}]
    [_root_.RingedSite.SameSite.HasPullbackDerived.{u, v, w, z}
      (O := R.ringSheafOfComm) (O' := R'.ringSheafOfComm)
      (CategoryTheory.Sheaf.ringSheafOfCommMap (𝒪₁ := R) (𝒪₂ := R') α)] :
    ModuleDerived.{z} (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) R) ⥤
      ModuleDerived.{z} (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) R') :=
  Chaotic.tensor.{z, u, v, w}
    (CategoryTheory.Sheaf.ringSheafOfCommMap (𝒪₁ := R) (𝒪₂ := R') α)

/-- The unit comparison in the commutative presentation, inherited from the underlying ring-sheaf
comparison. -/
@[stacks 08RX "commutative chaotic lower-shriek unit comparison"]
noncomputable abbrev unitComparison (α : R ⟶ R')
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C AddCommGrpCat.{w})
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat.{w}) (up ℤ))] :=
  Chaotic.unitComparison (CategoryTheory.Sheaf.ringSheafOfCommMap α)

/-- Source-facing object comparison for Lemma 21.39.12 after forgetting commutativity of the ring
sheaves. -/
@[stacks 08RX "commutative chaotic derived lower-shriek change of rings on objects"]
theorem lowerShriek_obj_isomorphic
    (α : R ⟶ R')
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C AddCommGrpCat.{w})
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat.{w}) (up ℤ))]
    (hUbullet : ∃ Ubullet : CosimplicialObject C,
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    [_root_.RingedSite.SameSite.HasPullbackDerived.{u, v, w, w}
      (CategoryTheory.Sheaf.ringSheafOfCommMap α)]
    [IsIso (unitComparison α)]
    (K : ModuleDerived.{w} (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) R)) :
    IsIsomorphic
      ((lowerShriek
        (X := RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) R)).obj K)
      ((lowerShriek
        (X := RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) R')).obj
        ((Chaotic.Comm.tensor α).obj K)) := sorry

end Comm

namespace Constant

variable {B : Type w} [Ring B]
variable {β : O ⟶ (constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B)}

/-- The derived functor in Remark 21.39.13: change scalars to the constant `B`-sheaf, present
modules as `B`-module-valued presheaves, and take the derived colimit to a point. -/
@[stacks 09CZ "chaotic constant-coefficient derived functor"]
noncomputable abbrev functor
    (O : Sheaf (⊥ : GrothendieckTopology C) RingCat.{w})
    (β : O ⟶ (constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B))
    [UnivLE.{max u v, z}]
    [_root_.RingedSite.SameSite.HasPullbackDerived.{u, v, w, z} β]
    [HasColimitsOfShape Cᵒᵖ (_root_.ModuleCat.{z} B)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C (_root_.ModuleCat.{z} B))
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ _root_.ModuleCat.{z} B) (up ℤ))] :
    ModuleDerived.{z} (RingedSite.ofRingSheaf (⊥ : GrothendieckTopology C) O) ⥤
      DerivedCategory (_root_.ModuleCat.{z} B) :=
  RingedSite.Hom.DerivedPoint.Chaotic.tensor β ⋙
    _root_.ModuleCat.Presheaf.Chaotic.Constant.derived (C := C) (B := B) ⋙
    categoryOverPointDerivedColimit C (_root_.ModuleCat.{z} B)

/-- Remark 21.39.13 (09CZ), comparison form: if the pointlike unit comparison is invertible, the
additive lower shriek is identified with the constant-coefficient functor followed by forgetting
the `B`-module structure. -/
@[stacks 09CZ "chaotic additive lower-shriek factorization"]
theorem factorization
    (O : Sheaf (⊥ : GrothendieckTopology C) RingCat.{w})
    (β : O ⟶ (constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B))
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C AddCommGrpCat.{w})
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ AddCommGrpCat.{w}) (up ℤ))]
    [HasColimitsOfShape Cᵒᵖ (_root_.ModuleCat.{w, w} B)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C (_root_.ModuleCat.{w, w} B))
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ _root_.ModuleCat.{w, w} B) (up ℤ))]
    [_root_.RingedSite.SameSite.HasPullbackDerived.{u, v, w, w} β]
    (hUbullet : ∃ Ubullet : CosimplicialObject C,
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    [IsIso (RingedSite.Hom.DerivedPoint.Chaotic.unitComparison β)] :
    IsIsomorphic
      (lowerShriek
        (X := RingedSite.ofRingSheaf (⊥ : GrothendieckTopology C) O))
      (functor.{w} O β ⋙ _root_.ModuleCat.forgetDerived B) := sorry

namespace functor

/-- The constant-coefficient functor carries a reusable triangulated-structure proposition. -/
@[stacks 09CZ "chaotic constant-coefficient triangulated functor"]
theorem hasTriangulatedStructure
    (O : Sheaf (⊥ : GrothendieckTopology C) RingCat.{w})
    (β : O ⟶ (constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B))
    [HasColimitsOfShape Cᵒᵖ (_root_.ModuleCat.{w, w} B)]
    [RingedSite.SameSite.HasPullbackDerived.{u, v, w, w} β]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C (_root_.ModuleCat.{w, w} B))
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ _root_.ModuleCat.{w, w} B) (up ℤ))] :
    (functor.{w} O β).HasTriangulatedStructure := sorry

end functor

namespace Comm

variable {R : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{w}}
variable {B : Type w} [CommRing B]

/-- The commutative source-facing map obtained by forgetting commutativity and identifying the
constant commutative sheaf with the constant `RingCat`-sheaf. -/
@[stacks 09CZ "commutative chaotic constant-coefficient ring map"]
noncomputable abbrev map
    (β : R ⟶ (constantSheaf (⊥ : GrothendieckTopology C) CommRingCat).obj
      (CommRingCat.of B)) :
    CategoryTheory.Sheaf.ringSheafOfComm R ⟶
      (constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B) :=
  CategoryTheory.Sheaf.ringSheafOfCommMap β ≫
    (_root_.ModuleCat.Presheaf.Chaotic.Constant.commRingSheafIso (C := C) (S := B)).hom

/-- The derived constant-coefficient functor in the commutative presentation. -/
@[stacks 09CZ "commutative chaotic constant-coefficient derived functor"]
noncomputable abbrev functor
    (R : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{w})
    (β : R ⟶ (constantSheaf (⊥ : GrothendieckTopology C) CommRingCat).obj
      (CommRingCat.of B))
    [UnivLE.{max u v, z}]
    [_root_.RingedSite.SameSite.HasPullbackDerived.{u, v, w, z}
      (Constant.Comm.map (C := C) (B := B) β)]
    [HasColimitsOfShape Cᵒᵖ (_root_.ModuleCat.{z} B)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C (_root_.ModuleCat.{z} B))
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ _root_.ModuleCat.{z} B) (up ℤ))] :
    ModuleDerived.{z} (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) R) ⥤
      DerivedCategory (_root_.ModuleCat.{z} B) :=
  Chaotic.tensor.{z, u, v, w} (Constant.Comm.map (C := C) (B := B) β) ⋙
    _root_.ModuleCat.Presheaf.Chaotic.Constant.derived (C := C) (B := B) ⋙
    categoryOverPointDerivedColimit C (_root_.ModuleCat.{z} B)

/-- Source-facing comparison for Remark 21.39.13 in the commutative presentation. -/
@[stacks 09CZ "commutative chaotic additive lower-shriek factorization"]
theorem factorization
    (R : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{w})
    (β : R ⟶ (constantSheaf (⊥ : GrothendieckTopology C) CommRingCat).obj
      (CommRingCat.of B))
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C AddCommGrpCat.{w})
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ AddCommGrpCat.{w}) (up ℤ))]
    [HasColimitsOfShape Cᵒᵖ (_root_.ModuleCat.{w, w} B)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C (_root_.ModuleCat.{w, w} B))
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ _root_.ModuleCat.{w, w} B) (up ℤ))]
    [_root_.RingedSite.SameSite.HasPullbackDerived.{u, v, w, w}
      (Constant.Comm.map (C := C) (B := B) β)]
    (hUbullet : ∃ Ubullet : CosimplicialObject C,
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    [IsIso (Chaotic.Comm.unitComparison β)] :
    IsIsomorphic
      (lowerShriek
        (X := RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) R))
      (functor.{w} R β ⋙ _root_.ModuleCat.forgetDerived B) := sorry

namespace functor

/-- The commutative source-facing constant-coefficient functor has a triangulated-structure
proposition, with no chosen shift comparison exposed in the public API. -/
@[stacks 09CZ "commutative chaotic constant-coefficient triangulated functor"]
theorem hasTriangulatedStructure
    (R : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{w})
    (β : R ⟶ (constantSheaf (⊥ : GrothendieckTopology C) CommRingCat).obj
      (CommRingCat.of B))
    [HasColimitsOfShape Cᵒᵖ (_root_.ModuleCat.{w, w} B)]
    [RingedSite.SameSite.HasPullbackDerived.{u, v, w, w}
      (Constant.Comm.map (C := C) (B := B) β)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C (_root_.ModuleCat.{w, w} B))
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ _root_.ModuleCat.{w, w} B) (up ℤ))] :
    (functor.{w} R β).HasTriangulatedStructure := sorry

end functor

end Comm

end Constant

end Chaotic

end RingedSite.Hom.DerivedPoint

end
