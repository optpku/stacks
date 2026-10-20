module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_29_2
public import stacks_project.Chap67.Lemma_67_15_2
public import stacks_project.Chap67.Lemma_67_23_3_Pullback
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin

/-!
# Purity of modules on algebraic spaces

Purity above a point excludes étale-neighbourhood impurities, while universal purity
excludes every scheme-valued impurity. Relative purity requires the corresponding
condition over every point of the base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A finite type quasi-coherent module is pure above `y` when it has no impurity along an
étale neighbourhood of `y`: every relative associated point of a scheme-valued étale base
change that lies over a generalization of the selected point specializes into the fibre. -/
def IsPureAlong (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) : Prop :=
  ∀ {T : Over S} (g : ofOver T ⟶ Y) (_ : AlgebraicSpace.Etale g)
    (t' t : T.left) (ξ : Points (Limits.pullback f g)),
    Specializes t' t →
      Points.map g (ofOver.pointsEquiv T t) = y →
        ξ ∈ relativeAssassin (Limits.pullback.snd f g)
            ((pullback (Limits.pullback.fst f g)).obj F) →
          Points.map (Limits.pullback.snd f g) ξ = ofOver.pointsEquiv T t' →
            ∃ θ : Points (Limits.pullback f g),
              Specializes ξ θ ∧
                Points.map (Limits.pullback.snd f g) θ = ofOver.pointsEquiv T t

/-- Purity above `y` is the absence of étale-neighbourhood impurities of `F` above `y`. -/
theorem isPureAlong_iff (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) :
    F.IsPureAlong f y ↔
      ∀ {T : Over S} (g : ofOver T ⟶ Y) (_ : AlgebraicSpace.Etale g)
        (t' t : T.left) (ξ : Points (Limits.pullback f g)),
        Specializes t' t →
          Points.map g (ofOver.pointsEquiv T t) = y →
            ξ ∈ relativeAssassin (Limits.pullback.snd f g)
                ((pullback (Limits.pullback.fst f g)).obj F) →
              Points.map (Limits.pullback.snd f g) ξ = ofOver.pointsEquiv T t' →
                ∃ θ : Points (Limits.pullback f g),
                  Specializes ξ θ ∧
                    Points.map (Limits.pullback.snd f g) θ =
                      ofOver.pointsEquiv T t :=
  sorry

/-- A finite type quasi-coherent module is universally pure above `y` when it has no
scheme-valued impurity above `y`. -/
def IsUniversallyPureAlong (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) : Prop :=
  ∀ {T : Over S} (g : ofOver T ⟶ Y) (t' t : T.left)
    (ξ : Points (Limits.pullback f g)),
    Specializes t' t →
      Points.map g (ofOver.pointsEquiv T t) = y →
        ξ ∈ relativeAssassin (Limits.pullback.snd f g)
            ((pullback (Limits.pullback.fst f g)).obj F) →
          Points.map (Limits.pullback.snd f g) ξ = ofOver.pointsEquiv T t' →
            ∃ θ : Points (Limits.pullback f g),
              Specializes ξ θ ∧
                Points.map (Limits.pullback.snd f g) θ = ofOver.pointsEquiv T t

/-- Universal purity above `y` is the absence of every scheme-valued impurity of `F`
above `y`. -/
theorem isUniversallyPureAlong_iff (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) :
    F.IsUniversallyPureAlong f y ↔
      ∀ {T : Over S} (g : ofOver T ⟶ Y) (t' t : T.left)
        (ξ : Points (Limits.pullback f g)),
        Specializes t' t →
          Points.map g (ofOver.pointsEquiv T t) = y →
            ξ ∈ relativeAssassin (Limits.pullback.snd f g)
                ((pullback (Limits.pullback.fst f g)).obj F) →
              Points.map (Limits.pullback.snd f g) ξ = ofOver.pointsEquiv T t' →
                ∃ θ : Points (Limits.pullback f g),
                  Specializes ξ θ ∧
                    Points.map (Limits.pullback.snd f g) θ =
                      ofOver.pointsEquiv T t :=
  sorry

/-- A finite type quasi-coherent module is pure relative to `Y` when it is pure above
every point of `Y`. -/
def IsPureOver (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] : Prop :=
  ∀ y : Points Y, F.IsPureAlong f y

/-- Relative purity is purity above every point of the base. -/
theorem isPureOver_iff (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] :
    F.IsPureOver f ↔ ∀ y : Points Y, F.IsPureAlong f y :=
  sorry

/-- A finite type quasi-coherent module is universally pure relative to `Y` when it is
universally pure above every point of `Y`. -/
def IsUniversallyPureOver (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] : Prop :=
  ∀ y : Points Y, F.IsUniversallyPureAlong f y

/-- Universal relative purity is universal purity above every point of the base. -/
theorem isUniversallyPureOver_iff (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType] :
    F.IsUniversallyPureOver f ↔ ∀ y : Points Y, F.IsUniversallyPureAlong f y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
