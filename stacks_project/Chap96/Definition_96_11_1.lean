/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Definition_96_11_1_QCoh
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

universe u

/- Definition 96.11.1: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in
groupoids. A quasi-coherent module on `𝒳`, or a quasi-coherent `𝒪_𝒳`-module,
is a quasi-coherent module on the ringed site `(𝒳_fppf, 𝒪_𝒳)` as in
Modules on Sites, Definition 18.23.1. -/
@[stacks 06WG] #check
  (fun {S : Scheme.{u}} (X : GroupoidsOver S)
      (M : RingedSite.ModuleCat.{u} (fppfRingedSite X)) ↦
    M.IsQuasicoherent)

/- The category of quasi-coherent sheaves on `𝒳` is denoted `QCoh(𝒪_𝒳)`. -/
@[stacks 06WG] #check (fun {S : Scheme.{u}} (X : GroupoidsOver S) ↦ QCoh X)

/- The forgetful inclusion `QCoh(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)`. -/
#check (fun {S : Scheme.{u}} (X : GroupoidsOver S) ↦ QCoh.inclusion X)
