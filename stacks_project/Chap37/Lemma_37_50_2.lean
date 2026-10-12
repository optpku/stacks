/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Over
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 37.50.2 (1): base change along `g : S' ⟶ S` gives a functor from projective
schemes over `S` to projective schemes over `S'`. -/
@[stacks 0B46] #check
  (AlgebraicGeometry.ProjectiveOver.baseChange :
    ∀ {S S' : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S),
      AlgebraicGeometry.ProjectiveOver S ⥤ AlgebraicGeometry.ProjectiveOver S')

/- Lemma 37.50.2 (2): a composite of projective scheme morphisms is projective. -/
@[stacks 0B46] #check
  (AlgebraicGeometry.Projective.comp :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} {f : Y ⟶ X} {g : X ⟶ S},
      AlgebraicGeometry.Projective f → AlgebraicGeometry.Projective g →
        AlgebraicGeometry.Projective (f ≫ g))

/- Lemma 37.50.2 (3): the structural morphism from the fibre product of two projective
schemes over the same base is projective. -/
@[stacks 0B46] #check
  (AlgebraicGeometry.Projective.fiberProduct :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S),
      AlgebraicGeometry.Projective f → AlgebraicGeometry.Projective g →
        AlgebraicGeometry.Projective (pullback.snd f g ≫ g))

/- Lemma 37.50.2 (4): over a base admitting an ample invertible module, the morphism
induced from a finite coproduct of projective schemes is projective. -/
@[stacks 0B46] #check
  (AlgebraicGeometry.Projective.sigmaDesc_of_hasAmpleInvertibleModule :
    ∀ {ι : Type u} [Finite ι] {S : AlgebraicGeometry.Scheme.{u}},
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule S →
        (X : ι → AlgebraicGeometry.Scheme.{u}) → (f : ∀ i, X i ⟶ S) →
          (∀ i, AlgebraicGeometry.Projective (f i)) →
            AlgebraicGeometry.Projective (Sigma.desc f))

/- Lemma 37.50.2 (5): every finite morphism of schemes is projective. -/
@[stacks 0B46] #check
  (AlgebraicGeometry.IsFinite.projective :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.IsFinite f → AlgebraicGeometry.Projective f)
