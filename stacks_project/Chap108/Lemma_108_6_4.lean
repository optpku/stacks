/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import stacks_project.Chap99.Proposition_99_3_10_Representable
public import stacks_project.Chap108.Lemma_108_5_2_Separated
public import stacks_project.Chap108.Lemma_108_5_10_Hilbert

/-!
# Lemma 108.6.4

The Hilbert Quot algebraic space of finitely presented quotients of a
finitely presented module, with Hilbert polynomial taken with respect to a
relatively ample invertible module, is separated of finite presentation over
the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonoidalCategory.InvertiblePower

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An invertible module `L` on an algebraic space `X` is relatively ample for a
morphism `f : X ⟶ Y` if `f` is representable by schemes and, after every base
change along a morphism from a scheme, the restricted pullback is relatively
ample in the scheme sense. -/
class RelativelyAmple {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (L : X.Modules) : Prop where
  /-- The morphism `f` is representable by schemes. -/
  representable : yoneda.relativelyRepresentable f
  /-- After any cartesian scheme base change, the restricted pullback is relatively
  ample as a module on schemes. -/
  ofScheme {Z W : Over S} {g : ofOver Z ⟶ Y} {pX : ofOver W ⟶ X} {pZ : W ⟶ Z} :
    IsPullback pX (ofOverMap pZ) f g →
      AlgebraicGeometry.RelativelyAmple pZ.left
        ((restrictFunctor (𝟙 (ofOver W)) ⋙ Quot.ofOverToScheme W).obj
          ((Modules.pullback pX).obj L))

/-- Relative ampleness over a morphism of algebraic spaces is representability of
the morphism together with scheme-relative ampleness after every scheme base
change. -/
theorem RelativelyAmple.iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) :
    RelativelyAmple f L ↔
      yoneda.relativelyRepresentable f ∧
        ∀ {Z W : Over S} {g : ofOver Z ⟶ Y} {pX : ofOver W ⟶ X} {pZ : W ⟶ Z},
          IsPullback pX (ofOverMap pZ) f g →
            AlgebraicGeometry.RelativelyAmple pZ.left
              ((restrictFunctor (𝟙 (ofOver W)) ⋙ Quot.ofOverToScheme W).obj
                ((Modules.pullback pX).obj L)) :=
  sorry

/-- A scheme morphism that is relatively ample in the scheme sense is relatively
ample as a morphism of algebraic spaces. -/
instance RelativelyAmple.ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    (L : (ofOver U).Modules)
    [AlgebraicGeometry.RelativelyAmple h.left
      ((restrictFunctor (𝟙 (ofOver U)) ⋙ Quot.ofOverToScheme U).obj L)] :
    RelativelyAmple (ofOverMap h) L :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- Lemma 108.6.4 (1): if `f : X ⟶ B` is a separated morphism of finite
presentation of algebraic spaces, `F` is a finitely presented `𝒪_X`-module, and
`L` is an invertible `𝒪_X`-module ample on `X/B` in the sense of
Definition 71.14.1, then the algebraic space `Quot^P_{F/X/B}` parametrizing
quotients of `F` with Hilbert polynomial `P` with respect to `L` is separated
over `B`. -/
@[stacks 0DPD]
instance instIsSeparatedOver_quotHilbert {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f] [Separated f] (F L : X.Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] [isInvertibleObject L]
    [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L] (P : ℤ → ℤ) :
    IsSeparatedOver (quotHilbert f F L P).toFunctor :=
  sorry

/-- Lemma 108.6.4 (2): if `f : X ⟶ B` is a separated morphism of finite
presentation of algebraic spaces, `F` is a finitely presented `𝒪_X`-module, and
`L` is an invertible `𝒪_X`-module ample on `X/B` in the sense of
Definition 71.14.1, then the algebraic space `Quot^P_{F/X/B}` parametrizing
quotients of `F` with Hilbert polynomial `P` with respect to `L` is of finite
presentation over `B`. -/
@[stacks 0DPD]
theorem quotHilbert_isFinitePresentationOver {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    [isInvertibleObject L] [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L]
    (P : ℤ → ℤ) :
    IsFinitePresentationOver (quotHilbert f F L P).toFunctor :=
  sorry

/-- Finite presentation of `quotHilbert` over `B` means some representing morphism
of algebraic spaces over `B` is of finite presentation. -/
theorem quotHilbert_isFinitePresentationOver_spec {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    [isInvertibleObject L] [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L]
    (P : ℤ → ℤ) :
    IsFinitePresentationOver (quotHilbert f F L P).toFunctor ↔
      ∃ (Q : AlgebraicSpace S) (π : Q ⟶ B),
        FinitePresentation π ∧
          Nonempty ((quotHilbert f F L P).toFunctor ≅ yonedaOver π) :=
  sorry

/-- The Hilbert locus is represented by a morphism of algebraic spaces over `B`
that is both separated and of finite presentation. -/
theorem quotHilbert_exists_separated_finitePresentation {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    [isInvertibleObject L] [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L]
    (P : ℤ → ℤ) :
    ∃ (Q : AlgebraicSpace S) (π : Q ⟶ B),
      Separated π ∧ FinitePresentation π ∧
        Nonempty ((quotHilbert f F L P).toFunctor ≅ yonedaOver π) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
