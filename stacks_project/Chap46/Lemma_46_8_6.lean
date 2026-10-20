module

public import ReasLib.Algebra.Category.ModuleCat.PureProjective.Resolution.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 46.8.6 (1): every module has a pure projective resolution. -/
@[stacks 0703] #check
  (ModuleCat.existsPureProjectiveResolution :
    ∀ {A : Type u} [CommRing A] (M : ModuleCat.{u} A),
      Nonempty (ModuleCat.PureProjectiveResolution M))

/- Lemma 46.8.6 (2): a map lifts from a pure projective resolution to any universally exact
resolution of its target. -/
@[stacks 0703] #check
  (ModuleCat.PureProjectiveResolution.existsLift :
    ∀ {A : Type u} [CommRing A] {M N : ModuleCat.{v} A}
      (P : ModuleCat.PureProjectiveResolution M)
      (Q : ModuleCat.UniversallyExactResolution N) (f : M ⟶ N),
      ∃ φ : P.complex ⟶ Q.complex, φ.f 0 ≫ Q.π = P.π ≫ f)

/- Lemma 46.8.6 (3): two lifts inducing the same map on resolved modules are homotopic. -/
@[stacks 0703] #check
  (ModuleCat.PureProjectiveResolution.homotopyOfLifts :
    ∀ {A : Type u} [CommRing A] {M N : ModuleCat.{v} A}
      (P : ModuleCat.PureProjectiveResolution M)
      (Q : ModuleCat.UniversallyExactResolution N) (f : M ⟶ N)
      (α β : P.complex ⟶ Q.complex)
      (hα : α.f 0 ≫ Q.π = P.π ≫ f) (hβ : β.f 0 ≫ Q.π = P.π ≫ f),
      homotopic (ModuleCat.{v} A) (ComplexShape.down ℕ) α β)
