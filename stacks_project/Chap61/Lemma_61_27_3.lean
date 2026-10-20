module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ProEtale.Constructible.Closure
import StacksCheckRecall

/-!
# Lemma 61.27.3

Constructible sheaves of `Λ`-modules on the small pro-étale site form a
weak Serre subcategory of `Mod(X_proétale, Λ)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type w) [Ring Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.ProEt),
    HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
    (ProEt.baseChange f).op.HasLeftKanExtension P]
variable [Abelian (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))]

/- Lemma 61.27.3: for a scheme `X` and a Noetherian ring `Λ`, the category of
constructible sheaves of `Λ`-modules on `X.ProEt` is a weak Serre subcategory of
`Sheaf (ProEt.topology X) (ModuleCat Λ)`. -/
@[stacks 09B5] #check
  (AlgebraicGeometry.Scheme.constructibleProEtaleModule_isWeakSerreClass X Λ :
    CategoryTheory.ObjectProperty.IsWeakSerreClass
      (AlgebraicGeometry.Scheme.constructibleProEtaleModule X Λ))

end AlgebraicGeometry.Scheme

end

end
