module

public import ReasLib.AlgebraicGeometry.GroupScheme.Action.Module.Quasicoherent

/-!
# Equivariant modules and change of base for action groupoids

This module compares equivariant quasi-coherent modules with quasi-coherent modules on the
associated action groupoid after changing the ambient base scheme.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.GroupoidScheme.System
open scoped CategoryTheory.Bicategory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh.Equivariant

/-- The cocycle condition for an equivariant module agrees with the cocycle condition after
regarding its action groupoid over the larger base scheme. -/
theorem actionGroupoidCocycle_iff {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G) (F : QCoh X.X.left)
    (alpha : (QCoh.pullback (action G X)).obj F ⟶
      (QCoh.pullback (projection G X)).obj F) :
    Cocycle G X F alpha ↔ GroupoidScheme.Cocycle (GroupoidScheme.action Y G X) F alpha := sorry

/-- The unit condition for an equivariant module agrees with the unit condition after
regarding its action groupoid over the larger base scheme. -/
theorem actionGroupoidUnit_iff {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G) (F : QCoh X.X.left)
    (alpha : (QCoh.pullback (action G X)).obj F ⟶
      (QCoh.pullback (projection G X)).obj F) :
    Unit G X F alpha ↔ GroupoidScheme.Unit (GroupoidScheme.action Y G X) F alpha := sorry

/-- Copy an equivariant module into the quasi-coherent-module category of its action groupoid
over the larger base scheme. -/
def toActionGroupoidObj {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) (D : Scheme.QCoh.Equivariant G X) :
    GroupoidScheme.QCoh (GroupoidScheme.action Y G X) :=
  GroupoidScheme.QCoh.of D.obj D.action
    ((actionGroupoidCocycle_iff Y G X D.obj D.action).mp D.cocycle)
    ((actionGroupoidUnit_iff Y G X D.obj D.action).mp D.unit)

/-- The copied underlying map is compatible with the action-groupoid linearizations. -/
theorem toActionGroupoidMap_compatibility {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    {D E : Scheme.QCoh.Equivariant G X} (f : D ⟶ E) :
    (QCoh.pullback (GroupoidScheme.action Y G X).t.left).map f.hom ≫
        (toActionGroupoidObj Y G X E).action =
      (toActionGroupoidObj Y G X D).action ≫
        (QCoh.pullback (GroupoidScheme.action Y G X).s.left).map f.hom := sorry

/-- Copy an equivariant morphism into the action-groupoid presentation. -/
def toActionGroupoidMap {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) {D E : Scheme.QCoh.Equivariant G X} (f : D ⟶ E) :
    toActionGroupoidObj Y G X D ⟶ toActionGroupoidObj Y G X E :=
  Hom.of f.hom (toActionGroupoidMap_compatibility Y G X f)

/-- Copying an identity morphism into the action-groupoid presentation preserves identity. -/
theorem toActionGroupoidMap_id {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : Scheme.QCoh.Equivariant G X) :
    toActionGroupoidMap Y G X (𝟙 D) = 𝟙 (toActionGroupoidObj Y G X D) := sorry

/-- Copying a composite into the action-groupoid presentation preserves composition. -/
theorem toActionGroupoidMap_comp {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    {D E F : Scheme.QCoh.Equivariant G X} (f : D ⟶ E) (g : E ⟶ F) :
    toActionGroupoidMap Y G X (f ≫ g) =
      toActionGroupoidMap Y G X f ≫ toActionGroupoidMap Y G X g := sorry

/-- The identity-on-data functor from equivariant modules to modules on the action groupoid. -/
def toActionGroupoid {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) :
    Scheme.QCoh.Equivariant G X ⥤ GroupoidScheme.QCoh (GroupoidScheme.action Y G X) where
  obj := toActionGroupoidObj Y G X
  map := toActionGroupoidMap Y G X
  map_id := toActionGroupoidMap_id Y G X
  map_comp := toActionGroupoidMap_comp Y G X

/-- Copy a module on an action groupoid back to the equivariant-module presentation. -/
def fromActionGroupoidObj {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G)
    (D : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)) :
    Scheme.QCoh.Equivariant G X :=
  Equivariant.of G X D.obj D.action
    ((actionGroupoidCocycle_iff Y G X D.obj D.action).mpr D.cocycle)
    ((actionGroupoidUnit_iff Y G X D.obj D.action).mpr D.unit)

/-- A copied action-groupoid morphism is compatible with the original linearizations. -/
theorem fromActionGroupoidMap_compatibility {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    {D E : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)} (f : D ⟶ E) :
    (QCoh.pullback (action G X)).map f.hom ≫
        (fromActionGroupoidObj Y G X E).action =
      (fromActionGroupoidObj Y G X D).action ≫
        (QCoh.pullback (projection G X)).map f.hom := sorry

/-- Copy an action-groupoid morphism back to the equivariant-module presentation. -/
def fromActionGroupoidMap {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G)
    {D E : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)} (f : D ⟶ E) :
    fromActionGroupoidObj Y G X D ⟶ fromActionGroupoidObj Y G X E :=
  Hom.of f.hom (fromActionGroupoidMap_compatibility Y G X f)

/-- Copying an identity morphism back to the equivariant presentation preserves identity. -/
theorem fromActionGroupoidMap_id {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)) :
    fromActionGroupoidMap Y G X (𝟙 D) = 𝟙 (fromActionGroupoidObj Y G X D) := sorry

/-- Copying a composite back to the equivariant presentation preserves composition. -/
theorem fromActionGroupoidMap_comp {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    {D E F : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)} (f : D ⟶ E) (g : E ⟶ F) :
    fromActionGroupoidMap Y G X (f ≫ g) =
      fromActionGroupoidMap Y G X f ≫ fromActionGroupoidMap Y G X g := sorry

/-- The identity-on-data functor from modules on the action groupoid back to equivariant modules. -/
def fromActionGroupoid {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) :
    GroupoidScheme.QCoh (GroupoidScheme.action Y G X) ⥤ Scheme.QCoh.Equivariant G X where
  obj := fromActionGroupoidObj Y G X
  map := fromActionGroupoidMap Y G X
  map_id := fromActionGroupoidMap_id Y G X
  map_comp := fromActionGroupoidMap_comp Y G X

/-- The identity underlying map is compatible with the linearizations on the source-side
round trip. -/
theorem actionGroupoidUnitHom_compatibility {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : Scheme.QCoh.Equivariant G X) :
    (QCoh.pullback (actionGroupoid G X).t.left).map (𝟙 D.obj) ≫
        (fromActionGroupoidObj Y G X (toActionGroupoidObj Y G X D)).action =
      D.action ≫ (QCoh.pullback (actionGroupoid G X).s.left).map (𝟙 D.obj) := sorry

/-- The identity underlying map gives the forward source-side round-trip comparison. -/
def actionGroupoidUnitHom {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) (D : Scheme.QCoh.Equivariant G X) :
    D ⟶ fromActionGroupoidObj Y G X (toActionGroupoidObj Y G X D) :=
  Hom.of (𝟙 D.obj)
    (actionGroupoidUnitHom_compatibility Y G X D)

/-- The identity underlying map is compatible with the reverse source-side round-trip
comparison. -/
theorem actionGroupoidUnitInv_compatibility {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : Scheme.QCoh.Equivariant G X) :
    (QCoh.pullback (actionGroupoid G X).t.left).map (𝟙 D.obj) ≫ D.action =
      (fromActionGroupoidObj Y G X (toActionGroupoidObj Y G X D)).action ≫
        (QCoh.pullback (actionGroupoid G X).s.left).map (𝟙 D.obj) := sorry

/-- The identity underlying map gives the reverse source-side round-trip comparison. -/
def actionGroupoidUnitInv {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) (D : Scheme.QCoh.Equivariant G X) :
    fromActionGroupoidObj Y G X (toActionGroupoidObj Y G X D) ⟶ D :=
  Hom.of (𝟙 D.obj)
    (actionGroupoidUnitInv_compatibility Y G X D)

/-- The source-side round-trip comparison followed by its inverse is the identity. -/
theorem actionGroupoidUnit_hom_inv_id {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : Scheme.QCoh.Equivariant G X) :
    actionGroupoidUnitHom Y G X D ≫ actionGroupoidUnitInv Y G X D = 𝟙 D := sorry

/-- The inverse source-side comparison followed by the comparison is the identity. -/
theorem actionGroupoidUnit_inv_hom_id {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : Scheme.QCoh.Equivariant G X) :
    actionGroupoidUnitInv Y G X D ≫ actionGroupoidUnitHom Y G X D =
      𝟙 (fromActionGroupoidObj Y G X (toActionGroupoidObj Y G X D)) := sorry

/-- The component of the source-side round-trip isomorphism. -/
def actionGroupoidUnitComponentIso {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : Scheme.QCoh.Equivariant G X) :
    D ≅ fromActionGroupoidObj Y G X (toActionGroupoidObj Y G X D) where
  hom := actionGroupoidUnitHom Y G X D
  inv := actionGroupoidUnitInv Y G X D
  hom_inv_id := actionGroupoidUnit_hom_inv_id Y G X D
  inv_hom_id := actionGroupoidUnit_inv_hom_id Y G X D

/-- The source-side round-trip components are natural. -/
theorem actionGroupoidUnit_naturality {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    {D E : Scheme.QCoh.Equivariant G X} (f : D ⟶ E) :
    f ≫ (actionGroupoidUnitComponentIso Y G X E).hom =
      (actionGroupoidUnitComponentIso Y G X D).hom ≫
        fromActionGroupoidMap Y G X (toActionGroupoidMap Y G X f) := sorry

/-- The unit isomorphism for the identity-on-data comparison functors. -/
def actionGroupoidUnitIso {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G) :
    𝟭 (Scheme.QCoh.Equivariant G X) ≅
      toActionGroupoid Y G X ⋙ fromActionGroupoid Y G X :=
  NatIso.ofComponents (actionGroupoidUnitComponentIso Y G X)
    (actionGroupoidUnit_naturality Y G X)

/-- The identity underlying map is compatible with the target-side round-trip
linearizations. -/
theorem actionGroupoidCounitHom_compatibility {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)) :
    (QCoh.pullback (GroupoidScheme.action Y G X).t.left).map (𝟙 D.obj) ≫ D.action =
      (toActionGroupoidObj Y G X (fromActionGroupoidObj Y G X D)).action ≫
        (QCoh.pullback (GroupoidScheme.action Y G X).s.left).map (𝟙 D.obj) := sorry

/-- The identity underlying map gives the forward target-side round-trip comparison. -/
def actionGroupoidCounitHom {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)) :
    toActionGroupoidObj Y G X (fromActionGroupoidObj Y G X D) ⟶ D :=
  Hom.of (𝟙 D.obj)
    (actionGroupoidCounitHom_compatibility Y G X D)

/-- The identity underlying map is compatible with the reverse target-side round-trip
comparison. -/
theorem actionGroupoidCounitInv_compatibility {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)) :
    (QCoh.pullback (GroupoidScheme.action Y G X).t.left).map (𝟙 D.obj) ≫
        (toActionGroupoidObj Y G X (fromActionGroupoidObj Y G X D)).action =
      D.action ≫
        (QCoh.pullback (GroupoidScheme.action Y G X).s.left).map (𝟙 D.obj) := sorry

/-- The identity underlying map gives the reverse target-side round-trip comparison. -/
def actionGroupoidCounitInv {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)) :
    D ⟶ toActionGroupoidObj Y G X (fromActionGroupoidObj Y G X D) :=
  Hom.of (𝟙 D.obj)
    (actionGroupoidCounitInv_compatibility Y G X D)

/-- The target-side round-trip comparison followed by its inverse is the identity. -/
theorem actionGroupoidCounit_hom_inv_id {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)) :
    actionGroupoidCounitHom Y G X D ≫ actionGroupoidCounitInv Y G X D =
      𝟙 (toActionGroupoidObj Y G X (fromActionGroupoidObj Y G X D)) := sorry

/-- The inverse target-side comparison followed by the comparison is the identity. -/
theorem actionGroupoidCounit_inv_hom_id {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)) :
    actionGroupoidCounitInv Y G X D ≫ actionGroupoidCounitHom Y G X D = 𝟙 D := sorry

/-- The component of the target-side round-trip isomorphism. -/
def actionGroupoidCounitComponentIso {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)) :
    toActionGroupoidObj Y G X (fromActionGroupoidObj Y G X D) ≅ D where
  hom := actionGroupoidCounitHom Y G X D
  inv := actionGroupoidCounitInv Y G X D
  hom_inv_id := actionGroupoidCounit_hom_inv_id Y G X D
  inv_hom_id := actionGroupoidCounit_inv_hom_id Y G X D

/-- The target-side round-trip components are natural. -/
theorem actionGroupoidCounit_naturality {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    {D E : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)} (f : D ⟶ E) :
    toActionGroupoidMap Y G X (fromActionGroupoidMap Y G X f) ≫
        (actionGroupoidCounitComponentIso Y G X E).hom =
      (actionGroupoidCounitComponentIso Y G X D).hom ≫ f := sorry

/-- The counit isomorphism for the identity-on-data comparison functors. -/
def actionGroupoidCounitIso {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G) :
    fromActionGroupoid Y G X ⋙ toActionGroupoid Y G X ≅
      𝟭 (GroupoidScheme.QCoh (GroupoidScheme.action Y G X)) :=
  NatIso.ofComponents (actionGroupoidCounitComponentIso Y G X)
    (actionGroupoidCounit_naturality Y G X)

/-- The unit and counit of the action-groupoid comparison satisfy the triangle identity. -/
theorem actionGroupoid_triangle {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G) :
    ∀ D,
      (toActionGroupoid Y G X).map ((actionGroupoidUnitIso Y G X).hom.app D) ≫
          (actionGroupoidCounitIso Y G X).hom.app ((toActionGroupoid Y G X).obj D) =
        𝟙 ((toActionGroupoid Y G X).obj D) := sorry

/-- The identity-on-module-and-linearization functors give an equivalence between equivariant
quasi-coherent modules and quasi-coherent modules on the associated action groupoid. -/
noncomputable def actionGroupoidEquivalence {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G) :
    CategoryTheory.Equivalence (Scheme.QCoh.Equivariant G X)
      (GroupoidScheme.QCoh (GroupoidScheme.action Y G X)) where
  functor := toActionGroupoid Y G X
  inverse := fromActionGroupoid Y G X
  unitIso := actionGroupoidUnitIso Y G X
  counitIso := actionGroupoidCounitIso Y G X
  functor_unitIso_comp := actionGroupoid_triangle Y G X

/-- The forward functor of the action-groupoid equivalence is the identity-on-data functor. -/
theorem actionGroupoidEquivalence_functor {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G) :
    (actionGroupoidEquivalence Y G X).functor = toActionGroupoid Y G X := sorry

/-- The inverse functor of the action-groupoid equivalence is the reverse identity-on-data
functor. -/
theorem actionGroupoidEquivalence_inverse {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G) :
    (actionGroupoidEquivalence Y G X).inverse = fromActionGroupoid Y G X := sorry

/-- The forward functor preserves the underlying quasi-coherent module. -/
theorem toActionGroupoid_obj_obj {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : Scheme.QCoh.Equivariant G X) :
    ((toActionGroupoid Y G X).obj D).obj = D.obj := sorry

/-- The forward functor preserves the linearization. -/
theorem toActionGroupoid_obj_action {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : Scheme.QCoh.Equivariant G X) :
    ((toActionGroupoid Y G X).obj D).action = D.action := sorry

/-- The forward functor preserves the underlying quasi-coherent-module morphism. -/
theorem toActionGroupoid_map_hom {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    {D E : Scheme.QCoh.Equivariant G X} (f : D ⟶ E) :
    ((toActionGroupoid Y G X).map f).hom = f.hom := sorry

/-- The inverse functor preserves the underlying quasi-coherent module. -/
theorem fromActionGroupoid_obj_obj {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)) :
    ((fromActionGroupoid Y G X).obj D).obj = D.obj := sorry

/-- The inverse functor preserves the linearization. -/
theorem fromActionGroupoid_obj_action {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    (D : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)) :
    ((fromActionGroupoid Y G X).obj D).action = D.action := sorry

/-- The inverse functor preserves the underlying quasi-coherent-module morphism. -/
theorem fromActionGroupoid_map_hom {S : Scheme.{u}} (Y : Over S)
    (G : Grp (Over Y.left)) (X : GroupScheme.Action G)
    {D E : GroupoidScheme.QCoh (GroupoidScheme.action Y G X)} (f : D ⟶ E) :
    ((fromActionGroupoid Y G X).map f).hom = f.hom := sorry

end AlgebraicGeometry.Scheme.QCoh.Equivariant
