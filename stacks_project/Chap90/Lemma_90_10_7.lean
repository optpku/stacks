module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Sections

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-Lemma 90.10.7-/
@[stacks 06IS] #check (CategoryTheory.Functor.exists_section_iff_exists_lift :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    [HasSchlessingerS2 p] (A : ArtinianLocalAlgCat Λ k) {y x xε x0 : F}
    (c : y ⟶ xε) (a : y ⟶ x) (e : xε ⟶ x0) (d : x ⟶ x0)
    (h_sq : CommSq c a e d)
    (hc : p.IsHomLift (dualNumberPullbackSnd A) c)
    (ha : p.IsHomLift (dualNumberPullbackFst A) a)
    (he : p.IsHomLift (dualNumberToResidue Λ k) e)
    (hd : p.IsHomLift (toResidue A) d),
    (∃ s : x ⟶ y, s ≫ a = 𝟙 x) ↔ (∃ sε : x ⟶ xε, sε ≫ e = d))

end CategoryTheory.Functor
