module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}}

/- Definition 59.71.1 (1): a sheaf of sets on `Xₑₜ` is constructible when every affine open admits
a finite constructible locally closed decomposition on which the restriction is finite locally
constant. -/
@[stacks 03RW] #check (CategoryTheory.Sheaf.IsConstructibleEtaleSet :
  (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
    Sheaf X.smallEtaleTopology (Type (u + 1)) →
      Sheaf Y.smallEtaleTopology (Type (u + 1))) →
  (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
    Sheaf Y.smallEtaleTopology (Type (u + 1)) → Prop) →
  Sheaf X.smallEtaleTopology (Type (u + 1)) → Prop)

/- Definition 59.71.1 (2): a sheaf of abelian groups on `Xₑₜ` is constructible when every affine
open admits a finite constructible locally closed decomposition on which the restriction is finite
locally constant. -/
@[stacks 03RW] #check (CategoryTheory.Sheaf.IsConstructibleEtaleAddCommGrp :
  (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} →
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) →
  (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop) →
  Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)

/- Definition 59.71.1 (3): for a Noetherian ring `Λ`, a sheaf of `Λ`-modules on `Xₑₜ` is
constructible when every affine open admits a finite constructible locally closed decomposition on
which the restriction is locally constant of finite type. -/
@[stacks 03RW] #check (CategoryTheory.Sheaf.IsConstructibleEtaleModule :
  {Λ : Type w} → [Ring Λ] → [IsNoetherianRing Λ] →
  (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
    Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ) →
      Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) →
  (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
    Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ) → Prop) →
  Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ) → Prop)

end CategoryTheory.Sheaf
