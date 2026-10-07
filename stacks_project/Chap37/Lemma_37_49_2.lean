module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Ample
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.49.2 (1): base change along `g : S' ⟶ S` gives a functor from
quasi-projective schemes over `S` to quasi-projective schemes over `S'`. -/
@[stacks 0B43] #check
  (AlgebraicGeometry.QuasiProjectiveOver.baseChange :
    ∀ {S S' : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S),
      AlgebraicGeometry.QuasiProjectiveOver S ⥤
        AlgebraicGeometry.QuasiProjectiveOver S')

/- Lemma 37.49.2 (2): a composite of quasi-projective scheme morphisms is quasi-projective
when the base admits an ample invertible module. -/
@[stacks 0B43] #check
  (AlgebraicGeometry.QuasiProjective.comp_of_hasAmpleInvertibleModule :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S},
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule S →
        AlgebraicGeometry.QuasiProjective f → AlgebraicGeometry.QuasiProjective g →
          AlgebraicGeometry.QuasiProjective (f ≫ g))

/- Lemma 37.49.2 (3): the structural morphism from the fibre product of two quasi-projective
schemes over a base with an ample invertible module is quasi-projective. -/
@[stacks 0B43] #check
  (AlgebraicGeometry.QuasiProjective.fiberProduct :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}},
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule S →
        (f : X ⟶ S) → (g : Y ⟶ S) →
          AlgebraicGeometry.QuasiProjective f → AlgebraicGeometry.QuasiProjective g →
            AlgebraicGeometry.QuasiProjective (pullback.snd f g ≫ g))

/- Lemma 37.49.2 (4): the morphism induced from a finite coproduct of quasi-projective
schemes over a base with an ample invertible module is quasi-projective. -/
@[stacks 0B43] #check
  (AlgebraicGeometry.QuasiProjective.sigmaDesc_of_hasAmpleInvertibleModule :
    ∀ {ι : Type u} [Finite ι] {S : AlgebraicGeometry.Scheme.{u}},
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule S →
        (X : ι → AlgebraicGeometry.Scheme.{u}) → (f : ∀ i, X i ⟶ S) →
          (∀ i, AlgebraicGeometry.QuasiProjective (f i)) →
            AlgebraicGeometry.QuasiProjective (Sigma.desc f))

/- Lemma 37.49.2 (5): every projective morphism is quasi-projective. -/
@[stacks 0B43] #check
  (AlgebraicGeometry.Projective.toQuasiProjective :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.Projective f → AlgebraicGeometry.QuasiProjective f)

/- Lemma 37.49.2 (6): every finite-type quasi-affine morphism is quasi-projective. -/
@[stacks 0B43] #check
  (AlgebraicGeometry.QuasiAffineHom.quasiProjective_of_finiteType :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
      [AlgebraicGeometry.Scheme.Hom.FiniteType f],
        AlgebraicGeometry.QuasiAffineHom f → AlgebraicGeometry.QuasiProjective f)

/- Lemma 37.49.2 (7): every separated quasi-finite morphism is quasi-projective. -/
@[stacks 0B43] #check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.quasiProjective :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.Scheme.Hom.QuasiFinite f → AlgebraicGeometry.IsSeparated f →
        AlgebraicGeometry.QuasiProjective f)

/- Lemma 37.49.2 (8): every quasi-compact immersion is quasi-projective. -/
@[stacks 0B43] #check
  (AlgebraicGeometry.IsImmersion.quasiProjective_of_quasiCompact :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.IsImmersion f → AlgebraicGeometry.QuasiCompact f →
        AlgebraicGeometry.QuasiProjective f)
