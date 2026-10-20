module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ExtensionByZero
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/- Lemma 61.26.6: if `j : U ⟶ X` is a quasi-compact open immersion of
schemes, then `abelianExtensionByZero j : Ab(U_proétale) ⥤ Ab(X_proétale)`
preserves limits. -/
@[stacks 09BP] #check
  (AlgebraicGeometry.Scheme.ProEt.abelianExtensionByZero_preservesLimits :
    ∀ {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    [∀ F : U.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology X) AddCommGrpCat.{u + 1}],
    PreservesLimits (abelianExtensionByZero j))

end AlgebraicGeometry.Scheme.ProEt
