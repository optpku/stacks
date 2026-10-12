/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import stacks_project.Chap78.Lemma_78_12_3_QCoh

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

/-- Equivariant morphisms form an additive commutative group under the pointwise
operations on their underlying module morphisms. -/
@[reducible]
def addCommGroup {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (M N : System G) : AddCommGroup (Hom M N) :=
  let zero : Zero (Hom M N) := ⟨of ⟨(0 : M.obj.obj ⟶ N.obj.obj)⟩ sorry⟩
  let add : Add (Hom M N) := ⟨fun f g ↦ of ⟨f.hom.hom + g.hom.hom⟩ sorry⟩
  let neg : Neg (Hom M N) := ⟨fun f ↦ of ⟨-f.hom.hom⟩ sorry⟩
  let sub : Sub (Hom M N) := ⟨fun f g ↦ of ⟨f.hom.hom - g.hom.hom⟩ sorry⟩
  let nsmul : SMul ℕ (Hom M N) := ⟨fun n f ↦ of ⟨n • f.hom.hom⟩ sorry⟩
  let zsmul : SMul ℤ (Hom M N) := ⟨fun n f ↦ of ⟨n • f.hom.hom⟩ sorry⟩
  @Function.Injective.addCommGroup (Hom M N) (M.obj.obj ⟶ N.obj.obj)
    add zero nsmul neg sub zsmul inferInstance (fun f ↦ f.hom.hom)
      (fun _ _ h ↦ ext (InducedCategory.hom_ext h)) rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Addition of equivariant morphisms is pointwise on the underlying module morphisms. -/
theorem addCommGroup_add_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {M N : System G} (f g : Hom M N) :
    ((addCommGroup M N).add f g).hom.hom = f.hom.hom + g.hom.hom := sorry

end System.Hom

namespace QCoh

/-- Equivariant quasi-coherent modules on a groupoid in algebraic spaces form a
preadditive category. -/
@[reducible]
def preadditive {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    Preadditive G.QCoh where
  homGroup M N := System.Hom.addCommGroup M N
  add_comp := sorry
  comp_add := sorry

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

/-- The category of equivariant quasi-coherent modules on a groupoid in algebraic
spaces is abelian when the source and target morphisms are flat. -/
instance instAbelian {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left] : Abelian G.QCoh :=
  abelian G

/-- The abelian structure is built from the native preadditive structure. -/
theorem abelian_toPreadditive {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left] :
    (abelian G).toPreadditive = preadditive G := sorry

/-- The underlying map of an equivariant morphism is the `System.Hom` field. -/
theorem hom_eq {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {M N : G.QCoh} (f : M ⟶ N) :
    hom f = (f : System.Hom M N).hom := sorry

end QCoh

end AlgebraicGeometry.GroupoidAlgebraicSpace
