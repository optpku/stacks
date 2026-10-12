/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Devissage
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ZeroObject

noncomputable section

universe u

/- Lemma 30.12.4: let `X` be a Noetherian scheme and let `P` be a property of coherent
`𝒪_X`-modules. If `P` contains zero, is invariant under isomorphisms of coherent modules, is
closed under extensions along short exact sequences of coherent modules, and holds for the
pushforward of every quasi-coherent ideal sheaf on every integral closed subscheme of `X`, then
`P` holds for every coherent module on `X`. -/
@[stacks 01YG] #check (
  AlgebraicGeometry.Scheme.Modules.coherent_property_of_shortExact_and_pushforward_ideal :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      (P : X.Modules → Prop)
      (h_zero : P (0 : X.Modules))
      (h_iso : ∀ {ℱ 𝒢 : X.Modules}, ℱ.IsCoherent → 𝒢.IsCoherent →
        (ℱ ≅ 𝒢) → P ℱ → P 𝒢)
      (h_shortExact :
        ∀ {S : ShortComplex X.Modules}, S.ShortExact →
          S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
          P S.X₁ → P S.X₃ → P S.X₂)
      (h_pushforward_ideal :
        ∀ (Z : X.IdealSheafData) (h_integral : IsIntegral Z.subscheme)
          (I : Subobject
            (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules)),
          (Subobject.underlying.obj I : Z.subscheme.Modules).IsQuasicoherent →
            P ((Scheme.Modules.pushforward Z.subschemeι).obj
              (Subobject.underlying.obj I : Z.subscheme.Modules)))
      (ℱ : X.Modules) [ℱ.IsCoherent],
      P ℱ)
