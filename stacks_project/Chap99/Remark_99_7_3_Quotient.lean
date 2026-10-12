/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subobject.Limits
public import stacks_project.Chap66.Lemma_66_29_2
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent

/-!
# Quasi-coherent quotients of a module on an algebraic space

A quasi-coherent quotient of a quasi-coherent module `F` on an algebraic space is an
epimorphism `F ⟶ Q` with `Q` quasi-coherent. Quotients are identified when they have
the same kernel.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A quasi-coherent quotient of a quasi-coherent `𝒪_X`-module `F`. -/
structure Quotient (F : X.Modules) [F.IsQuasicoherent] where
  /-- The target module sheaf of the quotient. -/
  module : X.Modules
  /-- The quotient morphism from `F`. -/
  map : F ⟶ module
  /-- The quotient morphism is an epimorphism. -/
  map_epi : Epi map
  /-- The target is quasi-coherent. -/
  isQuasicoherent : module.IsQuasicoherent

namespace Quotient

/-- Construct a quasi-coherent quotient from an epimorphism `F ⟶ Q` with `Q`
quasi-coherent. -/
def ofEpi (F : X.Modules) [F.IsQuasicoherent] (module : X.Modules) (map : F ⟶ module)
    (map_epi : Epi map) (isQuasicoherent : module.IsQuasicoherent) : Quotient F where
  module := module
  map := map
  map_epi := map_epi
  isQuasicoherent := isQuasicoherent

/-- A quasi-coherent quotient is an epimorphism onto a quasi-coherent module. -/
theorem spec {F : X.Modules} [F.IsQuasicoherent] (Q : Quotient F) :
    Epi Q.map ∧ Q.module.IsQuasicoherent := sorry

/-- Two quasi-coherent quotients of `F` are identified when they have the same kernel. -/
def Rel {F : X.Modules} [F.IsQuasicoherent] (Q₁ Q₂ : Quotient F) : Prop :=
  kernelSubobject Q₁.map = kernelSubobject Q₂.map

/-- Kernel equality is an equivalence relation on quasi-coherent quotients. -/
theorem rel_isEquivalence (F : X.Modules) [F.IsQuasicoherent] :
    Equivalence (fun Q₁ Q₂ : Quotient F ↦ Rel Q₁ Q₂) := sorry

/-- Kernel identification of quasi-coherent quotients is equivalent to an isomorphism of
targets over `F`. -/
theorem rel_iso_iff {F : X.Modules} [F.IsQuasicoherent] (Q₁ Q₂ : Quotient F) :
    Rel Q₁ Q₂ ↔ ∃ e : Q₁.module ≅ Q₂.module, Q₁.map ≫ e.hom = Q₂.map := sorry

/-- Precompose a quasi-coherent quotient with an isomorphism of its source. -/
def precomposeIso {F F' : X.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent]
    (e : F ≅ F') (Q : Quotient F') : Quotient F where
  module := Q.module
  map := e.hom ≫ Q.map
  map_epi := sorry
  isQuasicoherent := Q.isQuasicoherent

/-- The target of `precomposeIso e Q` is the target of `Q`. -/
theorem precomposeIso_module {F F' : X.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent]
    (e : F ≅ F') (Q : Quotient F') :
    (precomposeIso e Q).module = Q.module := sorry

/-- The underlying map of `precomposeIso e Q` is `e.hom ≫ Q.map`. -/
theorem precomposeIso_map {F F' : X.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent]
    (e : F ≅ F') (Q : Quotient F') :
    (precomposeIso e Q).map = e.hom ≫ Q.map := sorry

/-- Quasi-coherence is preserved by a composite of module pullbacks. -/
instance modulesPullback_comp_isQuasicoherent {Y W : AlgebraicSpace S}
    (f : Y ⟶ X) (p : W ⟶ Y) (F : X.Modules) [F.IsQuasicoherent] :
    ((Modules.pullback f ⋙ Modules.pullback p).obj F).IsQuasicoherent :=
  sorry

/-- Pull back a quasi-coherent quotient along a morphism of algebraic spaces. -/
def pullback {F : X.Modules} [F.IsQuasicoherent] (Q : Quotient F)
    {Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Quotient ((Modules.pullback f).obj F) where
  module := (Modules.pullback f).obj Q.module
  map := (Modules.pullback f).map Q.map
  map_epi := sorry
  isQuasicoherent := sorry

/-- The module of a pulled-back quotient is the module pullback of the original target. -/
theorem pullback_module {F : X.Modules} [F.IsQuasicoherent] (Q : Quotient F)
    {Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (Q.pullback f).module = (Modules.pullback f).obj Q.module := sorry

/-- Pullback preserves kernel identification of quasi-coherent quotients. -/
theorem rel_pullback {F : X.Modules} [F.IsQuasicoherent] {Q₁ Q₂ : Quotient F}
    (hQ : Rel Q₁ Q₂) {Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Rel (Q₁.pullback f) (Q₂.pullback f) := sorry

end Quotient

/-- The setoid of quasi-coherent quotients of `F` modulo kernel equality. -/
def quotientSetoid (F : X.Modules) [F.IsQuasicoherent] : Setoid (Quotient F) where
  r := Quotient.Rel
  iseqv := Quotient.rel_isEquivalence F

/-- Kernel-identified quasi-coherent quotients of `F`. -/
def quotients (F : X.Modules) [F.IsQuasicoherent] :=
  _root_.Quotient (quotientSetoid F)

/-- The setoid underlying `quotients F` is kernel equality of quasi-coherent quotients. -/
theorem quotients_mk (F : X.Modules) [F.IsQuasicoherent] :
    quotients F = _root_.Quotient (quotientSetoid F) := sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh

