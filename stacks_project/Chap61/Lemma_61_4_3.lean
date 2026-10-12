/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.IndZariski.Composition
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 61.4.3: if ring maps `A → B` and `B → C` are ind-Zariski, then the
composite `A → C` is ind-Zariski. -/
@[stacks 096Q] #check
  (RingHom.IndZariski.comp :
    ∀ {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B]
      [CommRing C] (f : A →+* B) (g : B →+* C),
      f.IndZariski → g.IndZariski → (g.comp f).IndZariski)

#check
  (RingHom.IndZariski.Raw.comp :
    ∀ {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B]
      [CommRing C] (f : A →+* B) (g : B →+* C)
      (hf : RingHom.IndZariski.Raw.{u, v, w} f)
      (hg : RingHom.IndZariski.Raw.{v, w, u} g),
      RingHom.IndZariski.Raw.{u, w, v} (g.comp f))
