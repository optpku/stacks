/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.Additive
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Abelian structure on equivariant quasi-coherent modules

Equivariant morphisms inherit pointwise addition from their underlying module
morphisms. When the source and target maps of a groupoid in algebraic spaces
are flat, its category of equivariant quasi-coherent modules is abelian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

namespace System.Hom

private theorem pullback_additive {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : (AlgebraicSpace.QCoh.pullback f).Additive := by
  letI : (AlgebraicSpace.Modules.pushforward f).Additive :=
    Functor.additive_of_preserves_binary_products _
  letI : (AlgebraicSpace.Modules.pullback f).Additive :=
    (AlgebraicSpace.Modules.pullbackPushforwardAdjunction f).left_adjoint_additive
  constructor
  intro M N g h
  apply InducedCategory.hom_ext
  change (AlgebraicSpace.Modules.pullback f).map (g.hom + h.hom) =
    (AlgebraicSpace.Modules.pullback f).map g.hom +
      (AlgebraicSpace.Modules.pullback f).map h.hom
  exact Functor.map_add _

attribute [local instance] pullback_additive

/-- Equivariant morphisms form an additive commutative group under the pointwise
operations on their underlying module morphisms. -/
@[reducible]
def addCommGroup {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (M N : System G) : AddCommGroup (Hom M N) :=
  let zero : Zero (Hom M N) := ⟨of ⟨(0 : M.obj.obj ⟶ N.obj.obj)⟩ (by
    change (AlgebraicSpace.QCoh.pullback G.t.left).map (0 : M.obj ⟶ N.obj) ≫ N.action =
      M.action ≫ (AlgebraicSpace.QCoh.pullback G.s.left).map (0 : M.obj ⟶ N.obj)
    simp)⟩
  let add : Add (Hom M N) := ⟨fun f g ↦ of ⟨f.hom.hom + g.hom.hom⟩ (by
    change (AlgebraicSpace.QCoh.pullback G.t.left).map (f.hom + g.hom) ≫ N.action =
      M.action ≫ (AlgebraicSpace.QCoh.pullback G.s.left).map (f.hom + g.hom)
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
      f.compatibility, g.compatibility])⟩
  let neg : Neg (Hom M N) := ⟨fun f ↦ of ⟨-f.hom.hom⟩ (by
    change (AlgebraicSpace.QCoh.pullback G.t.left).map (-f.hom) ≫ N.action =
      M.action ≫ (AlgebraicSpace.QCoh.pullback G.s.left).map (-f.hom)
    simp only [Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg,
      f.compatibility])⟩
  let sub : Sub (Hom M N) := ⟨fun f g ↦ of ⟨f.hom.hom - g.hom.hom⟩ (by
    change (AlgebraicSpace.QCoh.pullback G.t.left).map (f.hom - g.hom) ≫ N.action =
      M.action ≫ (AlgebraicSpace.QCoh.pullback G.s.left).map (f.hom - g.hom)
    simp only [Functor.map_sub, Preadditive.sub_comp, Preadditive.comp_sub,
      f.compatibility, g.compatibility])⟩
  let nsmul : SMul ℕ (Hom M N) := ⟨fun n f ↦ of ⟨n • f.hom.hom⟩ (by
    change (AlgebraicSpace.QCoh.pullback G.t.left).map (n • f.hom) ≫ N.action =
      M.action ≫ (AlgebraicSpace.QCoh.pullback G.s.left).map (n • f.hom)
    simp only [Functor.map_nsmul, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      f.compatibility])⟩
  let zsmul : SMul ℤ (Hom M N) := ⟨fun n f ↦ of ⟨n • f.hom.hom⟩ (by
    change (AlgebraicSpace.QCoh.pullback G.t.left).map (n • f.hom) ≫ N.action =
      M.action ≫ (AlgebraicSpace.QCoh.pullback G.s.left).map (n • f.hom)
    simp only [Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      f.compatibility])⟩
  @Function.Injective.addCommGroup (Hom M N) (M.obj.obj ⟶ N.obj.obj)
    add zero nsmul neg sub zsmul inferInstance (fun f ↦ f.hom.hom)
      (fun _ _ h ↦ ext (InducedCategory.hom_ext h)) rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Addition of equivariant morphisms is pointwise on the underlying module morphisms. -/
theorem addCommGroup_add_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {M N : System G} (f g : Hom M N) :
    ((addCommGroup M N).add f g).hom.hom = f.hom.hom + g.hom.hom := rfl

end System.Hom

namespace QCoh

/-- Equivariant quasi-coherent modules on a groupoid in algebraic spaces form a
preadditive category. -/
@[reducible]
def preadditive {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    Preadditive G.QCoh where
  homGroup M N := System.Hom.addCommGroup M N
  add_comp M N P f f' g := by
    apply System.Hom.ext
    apply InducedCategory.hom_ext
    change (f.hom.hom + f'.hom.hom) ≫ g.hom.hom =
      f.hom.hom ≫ g.hom.hom + f'.hom.hom ≫ g.hom.hom
    exact Preadditive.add_comp _ _ _ _ _ _
  comp_add M N P f g g' := by
    apply System.Hom.ext
    apply InducedCategory.hom_ext
    change f.hom.hom ≫ (g.hom.hom + g'.hom.hom) =
      f.hom.hom ≫ g.hom.hom + f.hom.hom ≫ g'.hom.hom
    exact Preadditive.comp_add _ _ _ _ _ _

/-- If the source and target morphisms of a groupoid in algebraic spaces are flat,
its category of equivariant quasi-coherent modules is abelian. -/
@[reducible]
def abelian {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left] : Abelian G.QCoh where
  toPreadditive := preadditive G
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- The abelian structure is built from the native preadditive structure. -/
theorem abelian_toPreadditive {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left] :
    (abelian G).toPreadditive = preadditive G := rfl

end QCoh

end AlgebraicGeometry.GroupoidAlgebraicSpace
