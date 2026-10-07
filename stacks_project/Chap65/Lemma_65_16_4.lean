module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Yoneda
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap65.Lemma_65_16_3_Equivalence
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace

/-!
# Lemma 65.16.4

Restriction of an fppf sheaf along `g : S ⟶ S'` is an algebraic space over `S` if and
only if the product of that sheaf with `h_S` is an algebraic space over `S'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The first projection of `j_!` of a restriction, sending a coproduct section to its index
morphism `φ : T' ⟶ S` over `S'`. -/
def extendBase_restriction_fst {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u) :
    extendBasePresheaf g (baseChangePresheaf g F') ⟶ yoneda.obj (Over.mk g) where
  app T' := ofHom fun σ ↦ σ.1
  naturality := fun _ _ _ ↦ sorry

/-- The second projection of `j_!` of a restriction, transporting the fiber section of `F'`
along `viewedIndexIso`. -/
def extendBase_restriction_snd {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u) :
    extendBasePresheaf g (baseChangePresheaf g F') ⟶ F' where
  app T' := ofHom fun σ ↦ F'.map (viewedIndexIso σ.1).inv.op σ.2
  naturality := fun _ _ _ ↦ sorry

/-- Package a morphism `φ : T' ⟶ S` over `S'` and a section of `F'` as a coproduct section of
`j_!` of the restriction of `F'`. -/
def extendBase_restriction_prodIso_inv_app {S S' : Scheme.{u}} {g : S ⟶ S'}
    (F' : (Over S')ᵒᵖ ⥤ Type u) {T' : Over S'} (φ : T' ⟶ Over.mk g)
    (t : F'.obj (op T')) :
    (extendBasePresheaf g (baseChangePresheaf g F')).obj (op T') :=
  ⟨φ, F'.map (viewedIndexIso φ).hom.op t⟩

/-- The inverse of `extendBase_restriction_prodIso`, splitting a product section into its
`h_S`-index and `F'`-component and transporting the latter back along `viewedIndexIso`. -/
def extendBase_restriction_prodIso_inv {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u) :
    yoneda.obj (Over.mk g) ⨯ F' ⟶ extendBasePresheaf g (baseChangePresheaf g F') where
  app T' := ofHom fun p ↦
    extendBase_restriction_prodIso_inv_app F'
      ((prod.fst : yoneda.obj (Over.mk g) ⨯ F' ⟶ yoneda.obj (Over.mk g)).app T' p)
      ((prod.snd : yoneda.obj (Over.mk g) ⨯ F' ⟶ F').app T' p)
  naturality := fun _ _ _ ↦ sorry

/-- The Sites matching identifying `j_!` of the restriction of `F'` with the product sheaf
`h_S × F'`. -/
def extendBase_restriction_prodIso {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u) :
    extendBasePresheaf g (baseChangePresheaf g F') ≅ yoneda.obj (Over.mk g) ⨯ F' where
  hom := prod.lift (extendBase_restriction_fst g F') (extendBase_restriction_snd g F')
  inv := extendBase_restriction_prodIso_inv g F'
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Lemma 65.16.4: let `g : S ⟶ S'` be a morphism of the big fppf site, and let `F'` be an
fppf sheaf on `(Sch/S')_fppf`. The restriction `baseChangePresheaf g F'` is an algebraic space
over `S` if and only if the product sheaf `yoneda.obj (Over.mk g) ⨯ F'` is an algebraic space
over `S'`. -/
@[stacks 04SH]
theorem isAlgebraicSpace_restriction_iff_prod {S S' : Scheme.{u}} (g : S ⟶ S')
    {F' : (Over S')ᵒᵖ ⥤ Type u}
    (hF' : Presheaf.IsSheaf (Scheme.fppfTopology.over S') F') :
    IsAlgebraicSpace (baseChangePresheaf g F') ↔
      IsAlgebraicSpace (yoneda.obj (Over.mk g) ⨯ F') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
