module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.KanExtension.Coskeleton
public import ReasLib.AlgebraicTopology.SimplexCategory.EpiMono.Biproduct
public import ReasLib.CategoryTheory.Limits.Shapes.Biproducts.Diagonal

/-!
# Biproduct model for the coskeleton of a concentrated truncated simplicial object

This leaf identifies each pointwise coskeleton limit with the biproduct indexed by monic simplex
morphisms and packages the identification naturally in the coefficient object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SimplexCategory
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A]

namespace concentrated.coskeleton.biproduct

variable [HasZeroObject A] [HasZeroMorphisms A]

namespace Internal

open coskeleton.Internal

/-- The top-degree cone leg out of the biproduct of monic maps `[k] ⟶ [n]`; it is zero when the
associated map is not monic. -/
private noncomputable def coneApp (B : A) {k n : ℕ}
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)]
    (j : StructuredArrow (op ⦋n⦌) (SimplexCategory.Truncated.inclusion k).op)
    (hX : j.right.unop.1.len = k) :
    (⨁ fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B) ⟶ (diagram B k n).obj j :=
  @dite _ (Mono (eqToHom (SimplexCategory.ext hX).symm ≫ j.hom.unop))
    (Classical.propDecidable _)
    (fun hf ↦
      Limits.biproduct.π (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)
          ⟨eqToHom (SimplexCategory.ext hX).symm ≫ j.hom.unop, hf⟩ ≫
        eqToHom (if_pos hX).symm)
    (fun _ ↦ 0)

/-- The raw component used to assemble the explicit biproduct-valued coskeleton cone. -/
private noncomputable def natTransApp (B : A) {k n : ℕ}
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)]
    (j : StructuredArrow (op ⦋n⦌) (SimplexCategory.Truncated.inclusion k).op) :
    (⨁ fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B) ⟶ (diagram B k n).obj j :=
  if hX : j.right.unop.1.len = k then coneApp B j hX else 0

/-- The raw coskeleton cone components `natTransApp B` are natural in the structured arrow. -/
private theorem natTrans_naturality (B : A) {k n : ℕ}
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)]
    {j j' : StructuredArrow (op ⦋n⦌) (SimplexCategory.Truncated.inclusion k).op}
    (φ : j ⟶ j') :
    ((Functor.const _).obj (⨁ fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)).map φ ≫
        natTransApp B j' =
      natTransApp B j ≫ (diagram B k n).map φ := sorry

/-- The natural transformation underlying the explicit biproduct-valued coskeleton cone. -/
private noncomputable def natTrans (B : A) (k n : ℕ)
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)] :
    (Functor.const _).obj (⨁ fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B) ⟶ diagram B k n where
  app := natTransApp B
  naturality _ _ φ := natTrans_naturality B φ

/-- A component of the coskeleton cone natural transformation is its explicit raw component. -/
@[simp]
private theorem natTrans.app (B : A) {k n : ℕ}
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)]
    (j : StructuredArrow (op ⦋n⦌) (SimplexCategory.Truncated.inclusion k).op) :
    (natTrans B k n).app j = natTransApp B j := sorry

/-- An explicit biproduct-valued cone on the pointwise coskeleton diagram. A leg is zero away
from top degree or when its associated map `[k] ⟶ [n]` is not monic. -/
private noncomputable def cone (B : A) (k n : ℕ)
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)] : Cone (diagram B k n) where
  pt := ⨁ fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B
  π := natTrans B k n

/-- The comparison from the pointwise coskeleton limit to its explicit biproduct model. -/
private noncomputable def limitToBiproduct (B : A) (k n : ℕ)
    [HasLimit (diagram B k n)]
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)] :
    limit (diagram B k n) ⟶ ⨁ fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B :=
  Limits.biproduct.lift fun f ↦
    limit.π (diagram B k n) (topArrow f) ≫ (topIso B k).inv

/-- The comparison from the explicit biproduct model to the pointwise coskeleton limit. -/
private noncomputable def biproductToLimit (B : A) (k n : ℕ)
    [HasLimit (diagram B k n)]
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)] :
    (⨁ fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B) ⟶ limit (diagram B k n) :=
  limit.lift (diagram B k n) (cone B k n)

/-- The coskeleton limit comparison followed by its inverse is the identity. -/
private theorem limitIso.hom_inv_id (B : A) (k n : ℕ)
    [HasLimit (diagram B k n)]
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)] :
    limitToBiproduct B k n ≫ biproductToLimit B k n =
      𝟙 (limit (diagram B k n)) := sorry

/-- The inverse coskeleton limit comparison followed by the comparison is the identity. -/
private theorem limitIso.inv_hom_id (B : A) (k n : ℕ)
    [HasLimit (diagram B k n)]
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)] :
    biproductToLimit B k n ≫ limitToBiproduct B k n =
      𝟙 (⨁ fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B) := sorry

/-- The pointwise coskeleton limit is explicitly isomorphic to the biproduct indexed by
monomorphisms `[k] ⟶ [n]`. -/
private noncomputable def limitIso (B : A) (k n : ℕ)
    [HasLimit (diagram B k n)]
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)] :
    limit (diagram B k n) ≅ ⨁ fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B where
  hom := limitToBiproduct B k n
  inv := biproductToLimit B k n
  hom_inv_id := limitIso.hom_inv_id B k n
  inv_hom_id := limitIso.inv_hom_id B k n

end Internal

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The hidden limit comparison used to define the public coskeleton biproduct decomposition. -/
private noncomputable def hiddenLimitIso (B : A) (k n : ℕ)
    [HasLimit (coskeleton.Internal.diagram B k n)]
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)] :
    limit (coskeleton.Internal.diagram B k n) ≅
      ⨁ fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B :=
  Internal.limitIso B k n

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The explicit degree-`n` biproduct decomposition of the coskeleton of `concentrated B k`. -/
@[stacks 0190 "degreewise coskeleton biproduct decomposition"]
noncomputable def iso (B : A) (k n : ℕ)
    [(concentrated B k).HasPointwiseCoskeleton]
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)] :
    (concentrated B k).coskeleton.obj (op ⦋n⦌) ≅
      ⨁ fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B :=
  (Functor.RightKanExtension.objIsoLimit
      (SimplexCategory.Truncated.inclusion k).op
      (concentrated B k) (op ⦋n⦌)).trans (hiddenLimitIso B k n)

/-- Under `biproduct.iso`, the canonical projection to the `f`-factor is `coskeleton.π B f`. -/
@[reassoc (attr := simp), stacks 0190 "coskeleton biproduct projection formula"]
theorem iso_hom_π (B : A) {k n : ℕ}
    [(concentrated B k).HasPointwiseCoskeleton]
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)] (f : MonoHom ⦋k⦌ ⦋n⦌) :
    (iso B k n).hom ≫ Limits.biproduct.π (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B) f =
      coskeleton.π B f := sorry

/-- The inverse coskeleton biproduct comparison recovers each canonical factor projection. -/
@[reassoc (attr := simp), stacks 0190 "inverse coskeleton biproduct projection formula"]
theorem iso_inv_π (B : A) {k n : ℕ}
    [(concentrated B k).HasPointwiseCoskeleton]
    [HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)] (f : MonoHom ⦋k⦌ ⦋n⦌) :
    (iso B k n).inv ≫ coskeleton.π B f =
      Limits.biproduct.π (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B) f := sorry

/-- The objectwise coskeleton biproduct comparisons are natural in the coefficient object. -/
@[stacks 0190 "concentrated coskeleton biproduct naturality"]
theorem iso.hom_naturality (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    {B D : A} (f : B ⟶ D) :
    (coskeleton.degree.functor (A := A) k n).map f ≫ (iso D k n).hom =
      (iso B k n).hom ≫
        (Limits.biproduct.diagonal (C := A) (MonoHom ⦋k⦌ ⦋n⦌)).map f := sorry

/-- The inverse coskeleton biproduct comparison is natural in the coefficient object. -/
@[reassoc (attr := simp), stacks 0190 "inverse concentrated coskeleton biproduct naturality"]
theorem iso.inv_naturality (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    {B D : A} (f : B ⟶ D) :
    (Limits.biproduct.diagonal (C := A) (MonoHom ⦋k⦌ ⦋n⦌)).map f ≫ (iso D k n).inv =
      (iso B k n).inv ≫ (coskeleton.degree.functor (A := A) k n).map f := sorry

/-- In a fixed simplicial degree, the coskeleton of the concentrated-object functor is naturally
isomorphic to the biproduct of its coefficient factors. -/
@[stacks 0190 "natural concentrated coskeleton biproduct decomposition"]
noncomputable def natIso (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] :
    coskeleton.degree.functor (A := A) k n ≅
      Limits.biproduct.diagonal (C := A) (MonoHom ⦋k⦌ ⦋n⦌) :=
  NatIso.ofComponents (fun B ↦ iso B k n)
    (fun f ↦ iso.hom_naturality k n f)

/-- A component of the natural coskeleton decomposition is the objectwise biproduct comparison. -/
@[simp, stacks 0190 "natural coskeleton decomposition component"]
theorem natIso.app (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] (B : A) :
    (natIso (A := A) k n).app B = iso B k n := sorry

/-- The forward component of the natural coskeleton decomposition is the objectwise comparison. -/
@[simp, stacks 0190 "natural coskeleton decomposition forward component"]
theorem natIso.hom_app (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] (B : A) :
    (natIso (A := A) k n).hom.app B = (iso B k n).hom := sorry

/-- The inverse component of the natural coskeleton decomposition is the inverse objectwise
comparison. -/
@[simp, stacks 0190 "natural coskeleton decomposition inverse component"]
theorem natIso.inv_app (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] (B : A) :
    (natIso (A := A) k n).inv.app B = (iso B k n).inv := sorry

/-- The natural coskeleton decomposition carries each canonical factor map to the corresponding
coefficient projection. -/
@[simp, stacks 0190 "natural coskeleton decomposition on factors"]
theorem natIso.hom_π {k n : ℕ}
    [∀ X : A, HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    (b : MonoHom ⦋k⦌ ⦋n⦌) :
    (natIso (A := A) k n).hom ≫ Limits.biproduct.diagonal.π (C := A) b =
      coskeleton.degree.π (A := A) b := sorry

/-- The inverse natural coskeleton decomposition carries each coefficient projection back to the
canonical coskeleton factor map. -/
@[simp, stacks 0190 "inverse natural coskeleton decomposition on factors"]
theorem natIso.inv_π {k n : ℕ}
    [∀ X : A, HasBiproduct (fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    (b : MonoHom ⦋k⦌ ⦋n⦌) :
    (natIso (A := A) k n).inv ≫ coskeleton.degree.π (A := A) b =
      Limits.biproduct.diagonal.π (C := A) b := sorry

end concentrated.coskeleton.biproduct

end CategoryTheory.SimplicialObject.Truncated
