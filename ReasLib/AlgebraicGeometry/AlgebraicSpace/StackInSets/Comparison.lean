module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets.Points
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Fiber
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Comparison

/-!
# Reindexing and postcomposition of scheme-valued points

The fibre objects associated to scheme-valued points are compatible with reindexing of
schemes and postcomposition by morphisms of algebraic spaces.
-/

@[expose] public section

-- Exposed constructions reference private proposition-valued laws for their explicit components.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry Opposite
open Functor CategoryTheory.CategoryOfElements

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The Yoneda transpose of a point commutes with precomposition by a scheme morphism. -/
private theorem objOfHomReindexIso_naturality {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T T' : Over S} (f : T' ⟶ T) (u : ofOver T ⟶ X) :
    X.functorOfPoints.map f.op (yonedaEquiv (u : yoneda.obj T ⟶ X.functorOfPoints)) =
      yonedaEquiv ((ofOverMap f ≫ u) : yoneda.obj T' ⟶ X.functorOfPoints) := sorry

/-- The category-of-elements arrow of a reindexed point is strongly cartesian. -/
private theorem objOfHomReindexIso_cartesian {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T T' : Over S} (f : T' ⟶ T) (u : ofOver T ⟶ X) :
    (stackInSets X).p.IsStronglyCartesian f
      (homMk
        ⟨op T, yonedaEquiv (u : yoneda.obj T ⟶ X.functorOfPoints)⟩
        ⟨op T', yonedaEquiv ((ofOverMap f ≫ u) : yoneda.obj T' ⟶ X.functorOfPoints)⟩
        f.op (objOfHomReindexIso_naturality f u)).op := by
  change ((π X.functorOfPoints).leftOp).IsStronglyCartesian f _
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · apply IsHomLift.of_fac' (π X.functorOfPoints).leftOp f _ rfl rfl
    rfl
  · intro a g φ hφ
    have hbase := @IsHomLift.eq_of_isHomLift _ _ _ _
      (π X.functorOfPoints).leftOp _ _ _ φ hφ
    change g ≫ f = φ.unop.val.unop at hbase
    have hpoint :
        X.functorOfPoints.map g.op
            (yonedaEquiv ((ofOverMap f ≫ u) : yoneda.obj T' ⟶ X.functorOfPoints)) =
          a.unop.snd := by
      rw [← objOfHomReindexIso_naturality f u]
      rw [← Functor.map_comp_apply]
      change X.functorOfPoints.map (g ≫ f).op _ = _
      rw [hbase]
      exact φ.unop.property
    refine ⟨(homMk _ _ g.op hpoint).op, ⟨?_, ?_⟩, ?_⟩
    · apply IsHomLift.of_fac' (π X.functorOfPoints).leftOp g _ rfl rfl
      rfl
    · apply Quiver.Hom.unop_inj
      apply Subtype.ext
      exact congrArg Quiver.Hom.op hbase
    · intro χ hχ
      apply Quiver.Hom.unop_inj
      apply Subtype.ext
      have hχbase := @IsHomLift.eq_of_isHomLift _ _ _ _
        (π X.functorOfPoints).leftOp _ _ _ χ hχ.1
      change g = χ.unop.val.unop at hχbase
      exact congrArg Quiver.Hom.op hχbase.symm

/-- The comparison of the explicit and selected cartesian lifts is vertical. -/
private theorem objOfHomReindexIso_over {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T T' : Over S} (f : T' ⟶ T) (u : ofOver T ⟶ X) :
    (stackInSets X).p.IsHomLift (𝟙 T')
      (IsStronglyCartesian.DomainIso.ofBaseIso (stackInSets X).p
        (g := Iso.refl T') (h := (Category.id_comp f).symm)
        (Chosen.cartesianHom (stackInSets X).p f (objOfHom u))
        (homMk
          ⟨op T, yonedaEquiv (u : yoneda.obj T ⟶ X.functorOfPoints)⟩
          ⟨op T', yonedaEquiv ((ofOverMap f ≫ u) : yoneda.obj T' ⟶ X.functorOfPoints)⟩
          f.op (objOfHomReindexIso_naturality f u)).op
        (Cleavage.cartesianHom.isStronglyCartesian
          (Cleavage.ofIsFibered (stackInSets X).p) f (objOfHom u))
        (objOfHomReindexIso_cartesian f u)).hom := sorry

/-- The fibre object of a precomposed point is canonically isomorphic to its reindexing. -/
def objOfHomReindexIso {S : Scheme.{u}} {X : AlgebraicSpace S} {T T' : Over S}
    (f : T' ⟶ T) (u : ofOver T ⟶ X) :
    objOfHom (ofOverMap f ≫ u) ≅ Chosen.reindexObj (stackInSets X).p f (objOfHom u) :=
  Fiber.isoMk
    (IsStronglyCartesian.DomainIso.ofBaseIso (stackInSets X).p
      (g := Iso.refl T') (h := (Category.id_comp f).symm)
      (Chosen.cartesianHom (stackInSets X).p f (objOfHom u))
      (homMk
        ⟨op T, yonedaEquiv (u : yoneda.obj T ⟶ X.functorOfPoints)⟩
        ⟨op T', yonedaEquiv ((ofOverMap f ≫ u) : yoneda.obj T' ⟶ X.functorOfPoints)⟩
        f.op (objOfHomReindexIso_naturality f u)).op
      (Cleavage.cartesianHom.isStronglyCartesian
        (Cleavage.ofIsFibered (stackInSets X).p) f (objOfHom u))
      (objOfHomReindexIso_cartesian f u))
    (objOfHomReindexIso_over f u)

/-- Postcomposition on the stack of points agrees with postcomposition of Yoneda transposes. -/
private theorem objOfHomMapIso_naturality {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : X ⟶ Y) {T : Over S} (r : ofOver T ⟶ X) :
    Y.functorOfPoints.map (Iso.refl (op T)).hom
      (((stackInSets.map φ).fiberFunctor T).obj (objOfHom r)).1.unop.snd =
        (objOfHom (r ≫ φ)).1.unop.snd := sorry

/-- The category-of-elements postcomposition comparison lies over the identity scheme map. -/
private theorem objOfHomMapIso_over {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : X ⟶ Y) {T : Over S} (r : ofOver T ⟶ X) :
    (stackInSets Y).p.IsHomLift (𝟙 T)
      (isoMk
        (((stackInSets.map φ).fiberFunctor T).obj (objOfHom r)).1.unop
        (objOfHom (r ≫ φ)).1.unop (Iso.refl _)
        (objOfHomMapIso_naturality φ r)).op.hom := sorry

/-- The fibre image of a point under postcomposition is the fibre object of the composite. -/
def objOfHomMapIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : X ⟶ Y) {T : Over S}
    (r : ofOver T ⟶ X) :
    ((stackInSets.map φ).fiberFunctor T).obj (objOfHom r) ≅ objOfHom (r ≫ φ) :=
  Fiber.isoMk
    (isoMk
      (((stackInSets.map φ).fiberFunctor T).obj (objOfHom r)).1.unop
      (objOfHom (r ≫ φ)).1.unop (Iso.refl _)
      (objOfHomMapIso_naturality φ r)).op
    (objOfHomMapIso_over φ r)

end AlgebraicGeometry.AlgebraicSpace
