module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.LocallyQuasiFinite.Module
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Etale

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/- Lemma 63.6.1 (1): Let `f : X ⟶ Y` be a locally quasi-finite morphism of
schemes. The functor `f_! : Ab(X_étale) ⥤ Ab(Y_étale)` has a right adjoint
`f^! : Ab(Y_étale) ⥤ Ab(X_étale)`, as the adjunction
`lowerShriek f ⊣ upperShriek f`. This `f^!` is the non-derived functor. -/
@[stacks 0F59]
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekAdjunction f :
  lowerShriek f ⊣ upperShriek f)

variable (ybar : GeometricPoint Y)
variable [HasProducts.{u} AddCommGrpCat.{u}]

/- Lemma 63.6.1 (2): for a locally quasi-finite morphism `f : X ⟶ Y` one has
`f^!(ȳ_* A) ≅ ∏_{f(x̄)=ȳ} x̄_* A`, naturally in the abelian group `A`, as the
isomorphism `upperShriekSkyscraperIso`. -/
@[stacks 0F59]
#check (AlgebraicGeometry.Scheme.Etale.upperShriekSkyscraperIso f ybar :
  (toSmallEtalePoint ybar).skyscraperSheafFunctor ⋙ upperShriek f ≅
    abelianSkyscraperProduct f ybar)

variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]

/- Lemma 63.6.1 (3): if `Λ` is a ring, then
`f_! : Mod(X_étale, Λ) ⥤ Mod(Y_étale, Λ)` has a right adjoint
`f^! : Mod(Y_étale, Λ) ⥤ Mod(X_étale, Λ)`, as the adjunction
`lowerShriekModule f Λ ⊣ upperShriekModule f Λ`. -/
@[stacks 0F59]
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekModuleAdjunction f Λ :
  lowerShriekModule f Λ ⊣ upperShriekModule f Λ)

variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/- Lemma 63.6.1 (4): the module-valued right adjoint `f^!` agrees with the
abelian `f^!` on underlying abelian sheaves, as the mate isomorphism
`upperShriekModule_forget` along `sheafCompose` of
`forget₂ (ModuleCat Λ) AddCommGrpCat`. -/
@[stacks 0F59]
#check (AlgebraicGeometry.Scheme.Etale.upperShriekModule_forget f Λ :
  upperShriekModule f Λ ⋙
      sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ≅
    sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
      upperShriek f)

end
