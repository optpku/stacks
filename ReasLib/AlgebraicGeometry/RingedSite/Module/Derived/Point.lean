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

The derived projection-to-a-point functor for module sheaves forgets module structure to
additive presheaves and then applies the total derived colimit. On chaotic sites, extension of
scalars compares these functors, and constant coefficients give a factorization through the
derived category of modules over the coefficient ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
-- Local instance justification (defeq pin): moduleHasDerivedCategory reduces to moduleCat_hasDerivedCategory and hence HasDerivedCategory.standard; registering this existing presentation spelling pins the same standard localization for SheafOfModules without selecting another derived model.
attribute [local instance] RingedSite.Hom.RingPresentation.moduleHasDerivedCategory
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

When the forgetful functor to additive presheaves is exact and the total left derived colimit
exists, their composite gives the derived projection to a point.
-/
@[stacks 08RX "derived lower shriek to a point"]
noncomputable abbrev lowerShriek
    [UnivLE.{max u v, z}]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [PreservesFiniteColimits
      (sheafToPresheaf X.siteTopology AddCommGrpCat.{z})]
    [HasColimitsOfShape X.carrierᵒᵖ AddCommGrpCat.{z}]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived X.carrier AddCommGrpCat.{z})
      (HomotopyCategory.quasiIso (X.carrierᵒᵖ ⥤ AddCommGrpCat.{z}) (up ℤ))] :
    ModuleDerived.{z} X ⥤ DerivedCategory AddCommGrpCat.{z} :=
  underlyingAbelianPresheafDerived.{z} X ⋙
    categoryOverPointDerivedColimit X.carrier AddCommGrpCat.{z}

end General

namespace Chaotic

variable {O O' : Sheaf (⊥ : GrothendieckTopology C) RingCat.{w}}
variable [UnivLE.{max u v, w}]

/-- Derived extension of scalars along a morphism of ring sheaves on a chaotic site. -/
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

/-- Given a pointlike cosimplicial object and an invertible unit comparison, derived extension
of scalars on a chaotic site preserves the lower-shriek functor to a point. -/
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

/-- Given a pointlike cosimplicial object and an invertible unit comparison, a complex and its
derived extension of scalars have isomorphic lower shrieks to a point. -/
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

/-- Derived extension of scalars along a morphism of commutative ring sheaves on a chaotic site,
formed by forgetting commutativity of the structure sheaves. -/
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

/-- Given a pointlike cosimplicial object and an invertible unit comparison, derived extension
of scalars along a commutative ring-sheaf map preserves the lower shriek of each complex. -/
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

/-- The constant-coefficient derived functor extends scalars to the constant `B`-sheaf,
identifies its module sheaves with `B`-module-valued presheaves, and takes the derived colimit
to a point. -/
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

/-- Given a pointlike cosimplicial object and an invertible unit comparison, the additive lower
shriek is isomorphic to the constant-coefficient functor followed by forgetting the `B`-module
structure. -/
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

/-- The constant-coefficient derived functor admits a triangulated structure. -/
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

/-- A map to a constant commutative ring sheaf induces a map of underlying ring sheaves to the
constant ring sheaf. -/
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

/-- Given a pointlike cosimplicial object and an invertible unit comparison, the additive lower
shriek for commutative ring sheaves factors, up to isomorphism, through the constant-coefficient
derived functor and the forgetful functor from `B`-modules. -/
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

/-- The constant-coefficient derived functor for commutative ring sheaves admits a triangulated
structure. -/
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
