/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.KanExtension.Skeleton
public import ReasLib.AlgebraicTopology.SimplexCategory.EpiMono.Biproduct
public import ReasLib.CategoryTheory.Limits.Shapes.Biproducts.Diagonal

/-!
# Biproduct model for the skeleton of a concentrated truncated simplicial object

This leaf identifies each pointwise skeleton colimit with the biproduct indexed by epic simplex
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

namespace concentrated.skeleton.biproduct

variable [HasZeroObject A] [HasZeroMorphisms A]

namespace Internal

open skeleton.Internal

/-- The top-degree cocone leg into the biproduct of epic maps `[n] ⟶ [k]`; it is zero when the
associated map is not epic. -/
private noncomputable def coconeApp (B : A) {k n : ℕ}
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)]
    (j : CostructuredArrow (SimplexCategory.Truncated.inclusion k).op (op ⦋n⦌))
    (hX : j.left.unop.1.len = k) :
    (diagram B k n).obj j ⟶ ⨁ fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B :=
  @dite _ (Epi (j.hom.unop ≫ eqToHom (SimplexCategory.ext hX)))
    (Classical.propDecidable _)
    (fun hf ↦
      eqToHom (if_pos hX) ≫
        Limits.biproduct.ι (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)
          ⟨j.hom.unop ≫ eqToHom (SimplexCategory.ext hX), hf⟩)
    (fun _ ↦ 0)

/-- The raw component used to assemble the explicit biproduct-valued skeleton cocone. -/
private noncomputable def natTransApp (B : A) {k n : ℕ}
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)]
    (j : CostructuredArrow (SimplexCategory.Truncated.inclusion k).op (op ⦋n⦌)) :
    (diagram B k n).obj j ⟶ ⨁ fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B :=
  if hX : j.left.unop.1.len = k then coconeApp B j hX else 0

/-- The raw skeleton cocone components `natTransApp B` are natural in the costructured arrow. -/
private theorem natTrans_naturality (B : A) {k n : ℕ}
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)]
    {j j' : CostructuredArrow (SimplexCategory.Truncated.inclusion k).op (op ⦋n⦌)}
    (φ : j ⟶ j') :
    (diagram B k n).map φ ≫ natTransApp B j' =
      natTransApp B j ≫
        ((Functor.const _).obj (⨁ fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)).map φ := sorry

/-- The natural transformation underlying the explicit biproduct-valued skeleton cocone. -/
private noncomputable def natTrans (B : A) (k n : ℕ)
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)] :
    diagram B k n ⟶ (Functor.const _).obj (⨁ fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B) where
  app := natTransApp B
  naturality _ _ φ := natTrans_naturality B φ

/-- A component of the skeleton cocone natural transformation is its explicit raw component. -/
private theorem natTrans.app (B : A) {k n : ℕ}
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)]
    (j : CostructuredArrow (SimplexCategory.Truncated.inclusion k).op (op ⦋n⦌)) :
    (natTrans B k n).app j = natTransApp B j := sorry

/-- An explicit biproduct-valued cocone on the pointwise skeleton diagram. A leg is zero away
from top degree or when its associated map `[n] ⟶ [k]` is not epic. -/
private noncomputable def cocone (B : A) (k n : ℕ)
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)] : Cocone (diagram B k n) where
  pt := ⨁ fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B
  ι := natTrans B k n

/-- The comparison from the pointwise skeleton colimit to its explicit biproduct model. -/
private noncomputable def colimitToBiproduct (B : A) (k n : ℕ)
    [HasColimit (diagram B k n)]
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)] :
    colimit (diagram B k n) ⟶ ⨁ fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B :=
  colimit.desc (diagram B k n) (cocone B k n)

/-- The comparison from the explicit biproduct model to the pointwise skeleton colimit. -/
private noncomputable def biproductToColimit (B : A) (k n : ℕ)
    [HasColimit (diagram B k n)]
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)] :
    (⨁ fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B) ⟶ colimit (diagram B k n) :=
  Limits.biproduct.desc fun f ↦
    (topIso B k).hom ≫ colimit.ι (diagram B k n) (topArrow f)

/-- The skeleton colimit comparison followed by its inverse is the identity. -/
private theorem colimitIso.hom_inv_id (B : A) (k n : ℕ)
    [HasColimit (diagram B k n)]
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)] :
    colimitToBiproduct B k n ≫ biproductToColimit B k n =
      𝟙 (colimit (diagram B k n)) := sorry

/-- The inverse skeleton colimit comparison followed by the comparison is the identity. -/
private theorem colimitIso.inv_hom_id (B : A) (k n : ℕ)
    [HasColimit (diagram B k n)]
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)] :
    biproductToColimit B k n ≫ colimitToBiproduct B k n =
      𝟙 (⨁ fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B) := sorry

/-- The pointwise skeleton colimit is explicitly isomorphic to the biproduct indexed by
epimorphisms `[n] ⟶ [k]`. -/
private noncomputable def colimitIso (B : A) (k n : ℕ)
    [HasColimit (diagram B k n)]
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)] :
    colimit (diagram B k n) ≅ ⨁ fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B where
  hom := colimitToBiproduct B k n
  inv := biproductToColimit B k n
  hom_inv_id := colimitIso.hom_inv_id B k n
  inv_hom_id := colimitIso.inv_hom_id B k n

end Internal

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Evaluate the private pointwise colimit comparison used by the public decomposition. -/
private noncomputable def buildIso (B : A) (k n : ℕ)
    [HasColimit (skeleton.Internal.diagram B k n)]
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)] :
    colimit (skeleton.Internal.diagram B k n) ≅
      ⨁ fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B :=
  Internal.colimitIso B k n

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The explicit degree-`n` biproduct decomposition of the skeleton of `concentrated B k`. -/
@[stacks 0190 "degreewise skeleton biproduct decomposition"]
noncomputable def iso (B : A) (k n : ℕ)
    [(concentrated B k).HasPointwiseSkeleton]
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)] :
    (concentrated B k).skeleton.obj (op ⦋n⦌) ≅
      ⨁ fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B :=
  ((SimplexCategory.Truncated.inclusion k).op.leftKanExtensionObjIsoColimit
      (concentrated B k) (op ⦋n⦌)).trans (buildIso B k n)

/-- Under `biproduct.iso`, `skeleton.ι B f` is the canonical inclusion of the `f`-summand. -/
@[reassoc (attr := simp), stacks 0190 "skeleton biproduct inclusion formula"]
theorem ι_iso_hom (B : A) {k n : ℕ}
    [(concentrated B k).HasPointwiseSkeleton]
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)] (f : EpiHom ⦋n⦌ ⦋k⦌) :
    skeleton.ι B f ≫ (iso B k n).hom =
      Limits.biproduct.ι (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B) f := sorry

/-- The inverse skeleton biproduct comparison recovers each canonical summand inclusion. -/
@[reassoc (attr := simp), stacks 0190 "inverse skeleton biproduct inclusion formula"]
theorem ι_iso_inv (B : A) {k n : ℕ}
    [(concentrated B k).HasPointwiseSkeleton]
    [HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)] (f : EpiHom ⦋n⦌ ⦋k⦌) :
    Limits.biproduct.ι (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B) f ≫ (iso B k n).inv =
      skeleton.ι B f := sorry

/-- The objectwise skeleton biproduct comparisons are natural in the coefficient object. -/
@[stacks 0190 "concentrated skeleton biproduct naturality"]
theorem iso.hom_naturality (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    {B D : A} (f : B ⟶ D) :
    (skeleton.degree.functor (A := A) k n).map f ≫ (iso D k n).hom =
      (iso B k n).hom ≫
        (Limits.biproduct.diagonal (C := A) (EpiHom ⦋n⦌ ⦋k⦌)).map f := sorry

/-- The inverse skeleton biproduct comparison is natural in the coefficient object. -/
@[reassoc (attr := simp), stacks 0190 "inverse concentrated skeleton biproduct naturality"]
theorem iso.inv_naturality (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    {B D : A} (f : B ⟶ D) :
    (Limits.biproduct.diagonal (C := A) (EpiHom ⦋n⦌ ⦋k⦌)).map f ≫ (iso D k n).inv =
      (iso B k n).inv ≫ (skeleton.degree.functor (A := A) k n).map f := sorry

/-- In a fixed simplicial degree, the skeleton of the concentrated-object functor is naturally
isomorphic to the biproduct of its coefficient summands. -/
@[stacks 0190 "natural concentrated skeleton biproduct decomposition"]
noncomputable def natIso (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k] :
    skeleton.degree.functor (A := A) k n ≅
      Limits.biproduct.diagonal (C := A) (EpiHom ⦋n⦌ ⦋k⦌) :=
  NatIso.ofComponents (fun B ↦ iso B k n)
    (fun f ↦ iso.hom_naturality k n f)

/-- A component of the natural skeleton decomposition is the objectwise biproduct comparison. -/
@[simp, stacks 0190 "natural skeleton decomposition component"]
theorem natIso.app (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k] (B : A) :
    (natIso (A := A) k n).app B = iso B k n := sorry

/-- The forward component of the natural skeleton decomposition is the objectwise comparison. -/
@[simp, stacks 0190 "natural skeleton decomposition forward component"]
theorem natIso.hom_app (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k] (B : A) :
    (natIso (A := A) k n).hom.app B = (iso B k n).hom := sorry

/-- The inverse component of the natural skeleton decomposition is the inverse objectwise
comparison. -/
@[simp, stacks 0190 "natural skeleton decomposition inverse component"]
theorem natIso.inv_app (k n : ℕ)
    [∀ X : A, HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k] (B : A) :
    (natIso (A := A) k n).inv.app B = (iso B k n).inv := sorry

/-- The natural skeleton decomposition carries each canonical summand map to the corresponding
coefficient inclusion. -/
@[simp, stacks 0190 "natural skeleton decomposition on summands"]
theorem natIso.ι_hom {k n : ℕ}
    [∀ X : A, HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    (a : EpiHom ⦋n⦌ ⦋k⦌) :
    skeleton.degree.ι (A := A) a ≫ (natIso (A := A) k n).hom =
      Limits.biproduct.diagonal.ι (C := A) a := sorry

/-- The inverse natural skeleton decomposition carries each coefficient inclusion back to the
canonical skeleton summand map. -/
@[simp, stacks 0190 "inverse natural skeleton decomposition on summands"]
theorem natIso.ι_inv {k n : ℕ}
    [∀ X : A, HasBiproduct (fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ X)]
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    (a : EpiHom ⦋n⦌ ⦋k⦌) :
    Limits.biproduct.diagonal.ι (C := A) a ≫ (natIso (A := A) k n).inv =
      skeleton.degree.ι (A := A) a := sorry

end concentrated.skeleton.biproduct

end CategoryTheory.SimplicialObject.Truncated
