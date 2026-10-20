module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.OpenImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

#check (AlgebraicGeometry.Scheme.Modules.pushforward :
  ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → X.Modules ⥤ Y.Modules)

#check (AlgebraicGeometry.moduleSpecΓFunctor :
  ∀ {R : CommRingCat.{u}}, (Spec (.of R)).Modules ⥤ ModuleCat R)

#check (AlgebraicGeometry.Scheme.Modules.pushforward.isQuasicoherent :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent],
    ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj F).IsQuasicoherent)

#check (AlgebraicGeometry.Scheme.Modules.fromTildeΓ :
  ∀ {R : CommRingCat.{u}} (M : (Spec (.of R)).Modules),
    tilde ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj M) ⟶ M)

#check (AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent :
  ∀ {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent],
    IsIso M.fromTildeΓ)

#check (CategoryTheory.asIso :
  ∀ {C : Type u} [Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [IsIso f], X ≅ Y)

#check (AlgebraicGeometry.Scheme.Modules.tildeGlobalSectionsRestrictMap :
  ∀ {A : Type u} [CommRing A] {U : Scheme.{u}}
    (j : U ⟶ Spec (.of A)) [IsOpenImmersion j] (ℱ : U.Modules),
    (tilde ((AlgebraicGeometry.moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      ((AlgebraicGeometry.Scheme.Modules.pushforward j).obj ℱ))).restrict j ⟶ ℱ)

/- Lemma 28.18.2: for a quasi-compact open immersion `j : U ⟶ Spec A` and a quasi-coherent
module `ℱ` on `U`, the canonical morphism obtained by restricting the affine reconstruction
map for `j_* ℱ` and composing with the restriction-pushforward counit is an isomorphism. -/
@[stacks 0EHM] #check
  (AlgebraicGeometry.Scheme.Modules.isIso_tildeGlobalSectionsRestrictMap :
    ∀ {A : Type u} [CommRing A] {U : Scheme.{u}}
      (j : U ⟶ Spec (.of A)) [IsOpenImmersion j] [QuasiCompact j]
      (ℱ : U.Modules) [ℱ.IsQuasicoherent],
      IsIso (AlgebraicGeometry.Scheme.Modules.tildeGlobalSectionsRestrictMap j ℱ))
