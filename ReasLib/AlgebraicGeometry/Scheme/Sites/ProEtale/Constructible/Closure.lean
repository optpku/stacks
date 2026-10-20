module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.ProEtaleComparison
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre

/-!
# Weak Serre closure of constructible pro-étale module sheaves

Constructible sheaves of modules over a Noetherian ring on the small pro-étale
site of a scheme form a weak Serre subcategory of all module sheaves.
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

/-- For a scheme `X` and a Noetherian ring `Λ`, constructible sheaves of
`Λ`-modules on the small pro-étale site form a weak Serre subcategory of
`Sheaf (ProEt.topology X) (ModuleCat Λ)`. -/
instance constructibleProEtaleModule_isWeakSerreClass :
    IsWeakSerreClass (constructibleProEtaleModule X Λ) :=
  sorry

end AlgebraicGeometry.Scheme

end

end
