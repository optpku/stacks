module

public import stacks_project.Chap63.Lemma_63_5_2_Trace

/-!
# Existence and uniqueness of weighting traces

Lemma 63.5.2: for a locally quasi-finite morphism `f : X ⟶ Y` of schemes and a
weighting `w : X → ℤ` of `f`, every abelian étale sheaf `F` on `Y` admits a
unique trace morphism `Tr_{f, w, F} : f_! f⁻¹ F ⟶ F` with the prescribed
stalkwise behaviour `⊕_{f(x̄)=ȳ} w(x̄)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- Lemma 63.5.2: Let `f : X ⟶ Y` be a locally quasi-finite morphism of schemes.
Let `w : X → ℤ` be a weighting of `f`. For any abelian sheaf `F` on `Y` there
exists a unique trace map `Tr_{f, w, F} : f_! f⁻¹ F ⟶ F` having the prescribed
behaviour on stalks. The morphism is `weightingTraceHom`, and the prescribed
stalk map is the weighted sum `⊕_{f(x̄)=ȳ} w(x̄)` after
`(f_! f⁻¹ F)_ȳ ≅ ⊕ (f⁻¹ F)_x̄ ≅ ⊕ F_ȳ`. Stacks locally quasi-finite is
rendered as `[LocallyQuasiFinite f]` together with `[LocallyOfFiniteType f]`. -/
@[stacks 0GKG]
def weightingTrace {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F) ⟶ F :=
  weightingTraceHom f hw F

/-- The source-facing trace morphism is the constructed sheaf map
`weightingTraceHom`. -/
theorem weightingTrace_eq {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    weightingTrace f hw F = weightingTraceHom f hw F :=
  sorry

/-- The prescribed stalk behaviour of `Tr_{f, w, F}`: after the identifications
`(f_! f⁻¹ F)_ȳ ≅ ⊕_{f(x̄)=ȳ} (f⁻¹ F)_x̄ ≅ ⊕_{f(x̄)=ȳ} F_ȳ`, the trace is the
weighted sum `⊕ w(x̄)`. -/
theorem weightingTrace_stalk {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (ybar : GeometricPoint Y) :
    (toSmallEtalePoint ybar).sheafFiber.map (weightingTrace f hw F) =
      (lowerShriekStalkIso f ybar).hom.app (weightingPullback f F) ≫
        (weightingPullbackStalkCoproductIso f ybar F).hom ≫
          weightingStalkDesc f w ybar F :=
  sorry

/-- Uniqueness of the weighting trace: a morphism `φ : f_! f⁻¹ F ⟶ F` agreeing
with the prescribed weighted sum on every geometric stalk equals
`weightingTrace`. -/
theorem weightingTrace_unique {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (φ : (lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F) ⟶ F)
    (hφ : ∀ ybar : GeometricPoint Y,
      (toSmallEtalePoint ybar).sheafFiber.map φ =
        (lowerShriekStalkIso f ybar).hom.app (weightingPullback f F) ≫
          (weightingPullbackStalkCoproductIso f ybar F).hom ≫
            weightingStalkDesc f w ybar F) :
    φ = weightingTrace f hw F :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
