module

public import ReasLib.AlgebraicGeometry.Scheme.SpreadingOut
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.SpreadingOut

/- Lemma 29.42.4 (1): if `Y` is locally of finite type over `S`, then two `S`-morphisms
`f, g : X ⟶ Y` with the same value at `x` and induced stalk map agree near `x`. -/
@[stacks 0BX6] #check
  (unique_of_locallyOfFiniteType :
    ∀ {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) [LocallyOfFiniteType fY]
      (f g : X ⟶ Y), f ≫ fY = fX → g ≫ fY = fX → ∀ {x : X},
      ∀ (hfgx : f x = g x),
        f.stalkMap x = Y.presheaf.stalkSpecializes (.of_eq hfgx.symm) ≫ g.stalkMap x →
          ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g)

/- Lemma 29.42.4 (2): the same uniqueness conclusion holds when `X` is integral. -/
@[stacks 0BX6] #check
  (fun {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) [IsIntegral X]
      (f g : X ⟶ Y) (hf : f ≫ fY = fX) (hg : g ≫ fY = fX) {x : X}
      (hfgx : f x = g x)
      (hstalk : f.stalkMap x = Y.presheaf.stalkSpecializes (.of_eq hfgx.symm) ≫ g.stalkMap x) ↦
    @unique_of_isGermInjective X Y S fX fY x (instIsGermInjectiveOfIsIntegral x)
      f g hf hg hfgx hstalk :
    ∀ {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) [IsIntegral X]
      (f g : X ⟶ Y), f ≫ fY = fX → g ≫ fY = fX → ∀ {x : X},
      ∀ (hfgx : f x = g x),
        f.stalkMap x = Y.presheaf.stalkSpecializes (.of_eq hfgx.symm) ≫ g.stalkMap x →
          ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g)

/- Lemma 29.42.4 (3): the same uniqueness conclusion holds when `X` is locally Noetherian. -/
@[stacks 0BX6] #check
  (fun {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) [IsLocallyNoetherian X]
      (f g : X ⟶ Y) (hf : f ≫ fY = fX) (hg : g ≫ fY = fX) {x : X}
      (hfgx : f x = g x)
      (hstalk : f.stalkMap x = Y.presheaf.stalkSpecializes (.of_eq hfgx.symm) ≫ g.stalkMap x) ↦
    @unique_of_isGermInjective X Y S fX fY x (instIsGermInjectiveOfIsLocallyNoetherian x)
      f g hf hg hfgx hstalk :
    ∀ {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) [IsLocallyNoetherian X]
      (f g : X ⟶ Y), f ≫ fY = fX → g ≫ fY = fX → ∀ {x : X},
      ∀ (hfgx : f x = g x),
        f.stalkMap x = Y.presheaf.stalkSpecializes (.of_eq hfgx.symm) ≫ g.stalkMap x →
          ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g)

/- Lemma 29.42.4 (4): the same uniqueness conclusion holds when `X` is reduced with finitely
many irreducible components. -/
@[stacks 0BX6] #check
  (fun {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) [IsReduced X]
      [Finite (irreducibleComponents X)] (f g : X ⟶ Y) (hf : f ≫ fY = fX)
      (hg : g ≫ fY = fX) {x : X} (hfgx : f x = g x)
      (hstalk : f.stalkMap x = Y.presheaf.stalkSpecializes (.of_eq hfgx.symm) ≫ g.stalkMap x) ↦
    @unique_of_isGermInjective X Y S fX fY x
      (Scheme.isGermInjective_of_isReduced_of_finite_irreducibleComponents X x)
      f g hf hg hfgx hstalk :
    ∀ {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) [IsReduced X]
      [Finite (irreducibleComponents X)] (f g : X ⟶ Y), f ≫ fY = fX → g ≫ fY = fX → ∀ {x : X},
      ∀ (hfgx : f x = g x),
        f.stalkMap x = Y.presheaf.stalkSpecializes (.of_eq hfgx.symm) ≫ g.stalkMap x →
          ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g)

/- Lemma 29.42.4 (5): compatible local stalk maps spread out when `Y` is locally of finite
presentation over `S`. -/
@[stacks 0BX6] #check
  (exists_of_locallyOfFinitePresentation :
    ∀ {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) [LocallyOfFinitePresentation fY]
      {x : X} {y : Y} (hxy : fX x = fY y) (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
      [IsLocalHom φ.hom],
      fY.stalkMap y ≫ φ = S.presheaf.stalkSpecializes (.of_eq hxy) ≫ fX.stalkMap x →
        ∃ (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y),
          Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f ∧
            f ≫ fY = U.ι ≫ fX)

/- Lemma 29.42.4 (6): the same existence conclusion holds when `Y` is locally of finite type
over `S` and `X` is integral. -/
@[stacks 0BX6] #check
  (fun {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) [LocallyOfFiniteType fY]
      [IsIntegral X] {x : X} {y : Y} (hxy : fX x = fY y)
      (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x) [IsLocalHom φ.hom]
      (hφ : fY.stalkMap y ≫ φ = S.presheaf.stalkSpecializes (.of_eq hxy) ≫ fX.stalkMap x) ↦
    @exists_of_isGermInjective X Y S fX fY _ x (instIsGermInjectiveOfIsIntegral x) y hxy φ _ hφ :
    ∀ {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) [LocallyOfFiniteType fY]
      [IsIntegral X] {x : X} {y : Y} (hxy : fX x = fY y)
      (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x) [IsLocalHom φ.hom],
      fY.stalkMap y ≫ φ = S.presheaf.stalkSpecializes (.of_eq hxy) ≫ fX.stalkMap x →
        ∃ (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y),
          Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f ∧ f ≫ fY = U.ι ≫ fX)

/- Lemma 29.42.4 (7): the same existence conclusion holds when `Y` is locally of finite type
over `S` and `X` is locally Noetherian. -/
@[stacks 0BX6] #check
  (fun {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) [LocallyOfFiniteType fY]
      [IsLocallyNoetherian X] {x : X} {y : Y} (hxy : fX x = fY y)
      (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x) [IsLocalHom φ.hom]
      (hφ : fY.stalkMap y ≫ φ = S.presheaf.stalkSpecializes (.of_eq hxy) ≫ fX.stalkMap x) ↦
    @exists_of_isGermInjective X Y S fX fY _ x (instIsGermInjectiveOfIsLocallyNoetherian x) y hxy φ _ hφ :
    ∀ {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) [LocallyOfFiniteType fY]
      [IsLocallyNoetherian X] {x : X} {y : Y} (hxy : fX x = fY y)
      (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x) [IsLocalHom φ.hom],
      fY.stalkMap y ≫ φ = S.presheaf.stalkSpecializes (.of_eq hxy) ≫ fX.stalkMap x →
        ∃ (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y),
          Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f ∧ f ≫ fY = U.ι ≫ fX)

/- Lemma 29.42.4 (8): the same existence conclusion holds when `Y` is locally of finite type
over `S` and `X` is reduced with finitely many irreducible components. -/
@[stacks 0BX6] #check
  (fun {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) [LocallyOfFiniteType fY]
      [IsReduced X] [Finite (irreducibleComponents X)] {x : X} {y : Y} (hxy : fX x = fY y)
      (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x) [IsLocalHom φ.hom]
      (hφ : fY.stalkMap y ≫ φ = S.presheaf.stalkSpecializes (.of_eq hxy) ≫ fX.stalkMap x) ↦
    @exists_of_isGermInjective X Y S fX fY _ x
      (Scheme.isGermInjective_of_isReduced_of_finite_irreducibleComponents X x)
      y hxy φ _ hφ :
    ∀ {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S) [LocallyOfFiniteType fY]
      [IsReduced X] [Finite (irreducibleComponents X)] {x : X} {y : Y} (hxy : fX x = fY y)
      (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x) [IsLocalHom φ.hom],
      fY.stalkMap y ≫ φ = S.presheaf.stalkSpecializes (.of_eq hxy) ≫ fX.stalkMap x →
        ∃ (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y),
          Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f ∧ f ≫ fY = U.ι ≫ fX)

end AlgebraicGeometry.SpreadingOut
