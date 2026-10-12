/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap75.Definition_75_20_2_TorIndependence
public import stacks_project.Chap92.«92_28_0_1_FibreProduct»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibre-product cotangent complex of Tor-independent algebraic spaces

If `X` and `Y` are Tor-independent algebraic spaces over `B`, the fibre-product cone
`E` of (92.28.0.1) vanishes in `D(𝒪_{X ×_B Y})`, and `sumMap` is an isomorphism.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent
namespace FibreProduct

/-- Lemma 92.28.1 (1): if `X` and `Y` are Tor independent over `B`, then the
object `E` in (92.28.0.1) is zero in `D(𝒪_{X ×_B Y})`. -/
@[stacks 09DL]
theorem cone_isZero_of_torIndependent {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B)
    (h_torIndependent : TorIndependentOver (Over.mk f) (Over.mk g)) :
    IsZero (cone f g) :=
  sorry

/-- Lemma 92.28.1 (2): if `X` and `Y` are Tor independent over `B`, then
`L_{X ×_B Y / B}` is isomorphic in `D(𝒪_{X ×_B Y})` to the derived biproduct
`Lp^* L_{X/B} ⊕ Lq^* L_{Y/B}`, as invertibility of `sumMap f g`. This
isomorphism is represented by the cochain biproduct
`pullbackCotangentCochain (pullback.fst f g) f ⊞
pullbackCotangentCochain (pullback.snd f g) g` of `𝒪_{X ×_B Y}`-modules. -/
@[stacks 09DL]
theorem sumMap_isIso_of_torIndependent {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B)
    (h_torIndependent : TorIndependentOver (Over.mk f) (Over.mk g)) :
    IsIso (sumMap f g) :=
  sorry

/-- Object-level form of invertibility of `sumMap`: `cotangent (toBase f g)` is
isomorphic to `DerivedCategory.Q.obj` of the cochain biproduct
`pullbackCotangentCochain (pullback.fst f g) f ⊞
pullbackCotangentCochain (pullback.snd f g) g`. -/
theorem isIsomorphic_cotangent_sumMapSource_of_torIndependent
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (h_torIndependent : TorIndependentOver (Over.mk f) (Over.mk g)) :
    IsIsomorphic (cotangent (toBase f g))
      (DerivedCategory.Q.obj
        (pullbackCotangentCochain (pullback.fst f g) f ⊞
          pullbackCotangentCochain (pullback.snd f g) g)) :=
  sorry

end FibreProduct
end AlgebraicGeometry.AlgebraicSpace.Cotangent
