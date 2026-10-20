module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.Equivalence

/-!
# Restriction and products of algebraic spaces

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

/-- The inverse of `extendBase_restriction_prodIso`, splitting a product section into its
`h_S`-index and `F'`-component and transporting the latter back along `viewedIndexIso`. -/
def extendBase_restriction_prodIso_inv {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u) :
    yoneda.obj (Over.mk g) ⨯ F' ⟶ extendBasePresheaf g (baseChangePresheaf g F') where
  app T' := ofHom fun p ↦
    let φ := (prod.fst : yoneda.obj (Over.mk g) ⨯ F' ⟶ yoneda.obj (Over.mk g)).app T' p
    let t := (prod.snd : yoneda.obj (Over.mk g) ⨯ F' ⟶ F').app T' p
    ⟨φ, F'.map (viewedIndexIso φ).hom.op t⟩
  naturality := fun _ _ _ ↦ sorry

/-- Coproduct extension of the restriction of a presheaf is naturally isomorphic to its
product with the presheaf represented by the base morphism. -/
def extendBase_restriction_prodIso {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u) :
    extendBasePresheaf g (baseChangePresheaf g F') ≅ yoneda.obj (Over.mk g) ⨯ F' :=
  let hom := prod.lift (extendBase_restriction_fst g F') (extendBase_restriction_snd g F')
  let inv := extendBase_restriction_prodIso_inv g F'
  let laws : (hom ≫ inv = 𝟙 (extendBasePresheaf g (baseChangePresheaf g F'))) ∧
      (inv ≫ hom = 𝟙 (yoneda.obj (Over.mk g) ⨯ F')) := sorry
  { hom := hom
    inv := inv
    hom_inv_id := laws.1
    inv_hom_id := laws.2 }

/-- Let `g : S ⟶ S'` be a morphism of schemes, and let `F'` be an
fppf sheaf on `(Sch/S')_fppf`. The restriction `baseChangePresheaf g F'` is an algebraic space
over `S` if and only if the product sheaf `yoneda.obj (Over.mk g) ⨯ F'` is an algebraic space
over `S'`. -/
theorem isAlgebraicSpace_restriction_iff_prod {S S' : Scheme.{u}} (g : S ⟶ S')
    {F' : (Over S')ᵒᵖ ⥤ Type u}
    (hF' : Presheaf.IsSheaf (Scheme.fppfTopology.over S') F') :
    IsAlgebraicSpace (baseChangePresheaf g F') ↔
      IsAlgebraicSpace (yoneda.obj (Over.mk g) ⨯ F') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
