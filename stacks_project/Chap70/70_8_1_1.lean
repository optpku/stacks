/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.ExtendOpen
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

universe u

/- 70.8.1.1: for a later-to-earlier transition of glued étale relations, the
square R ⟶ R', V ⟶ V' with vertical maps s, s' is cartesian. Here R is the
open-immersion pushout of the diagonal of a representable étale chart against
W ⟶ V, and s : R ⟶ V extends the second projection of W ×_U W. Presheaf
bases include the algebraic spaces U_i in the construction. The cartesian
open-subscheme hypothesis is the inverse-image condition of the approximation
lemma applied to W ⊆ V. -/
@[stacks 07SV] #check (AlgebraicGeometry.Scheme.PreRelation.ExtendOpen.source_isPullback :
  ∀ {W V W' V' : Scheme.{u}} {U U' : Scheme.{u}ᵒᵖ ⥤ Type u}
    (ιW : W ⟶ V) (w : yoneda.obj W ⟶ U) (hw : MorphismProperty.presheaf (@Etale) w)
    (ιW' : W' ⟶ V') (w' : yoneda.obj W' ⟶ U') (hw' : MorphismProperty.presheaf (@Etale) w')
    [IsOpenImmersion ιW] [IsOpenImmersion ιW']
    (hW : W ⟶ W') (v : V ⟶ V') (u : U ⟶ U')
    (hWU : IsPullback (yoneda.map hW) w w' u) (hWV : IsPullback ιW hW v ιW'),
    IsPullback (AlgebraicGeometry.Scheme.PreRelation.ExtendOpen.map
      ιW w hw ιW' w' hw' hW v u hWU hWV)
      (AlgebraicGeometry.Scheme.PreRelation.ExtendOpen.source ιW w hw)
      (AlgebraicGeometry.Scheme.PreRelation.ExtendOpen.source ιW' w' hw') v)
