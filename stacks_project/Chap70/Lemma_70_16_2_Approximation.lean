module

public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap70.Lemma_70_11_2_Approximation

/-!
# Integral finite approximation of algebraic spaces, refined over an open

An integral morphism of algebraic spaces over a scheme `S`, with quasi-compact
quasi-separated target, may be realized as a directed inverse limit of finite
morphisms of finite presentation into that target, with the inverse image of a
given quasi-compact open remaining isomorphic at every stage.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `h : X ⟶ Z` over `Y` induces a commuting square of inverse
images of an open immersion `ι : V ⟶ Y`. -/
theorem openInverseImage_comp_eq {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) (h : X ⟶ Z) (ι : V ⟶ Y) [IsOpenImmersion ι]
    (w : h ≫ g = f) :
    (openInverseImageι f ι ≫ h) ≫ g = openInverseImageTo f ι ≫ ι :=
  sorry

/-- The comparison `f⁻¹V ⟶ g⁻¹V` induced by a morphism `h : X ⟶ Z` over `Y`. -/
def openInverseImageMap {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) (h : X ⟶ Z) (ι : V ⟶ Y) [IsOpenImmersion ι]
    (w : h ≫ g = f) :
    openInverseImage f ι ⟶ openInverseImage g ι :=
  (openInverseImage_isPullback g ι).lift (openInverseImageι f ι ≫ h)
    (openInverseImageTo f ι) (openInverseImage_comp_eq f g h ι w)

/-- `openInverseImageMap` commutes with the open-subspace inclusions. -/
theorem openInverseImageMap_ι {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) (h : X ⟶ Z) (ι : V ⟶ Y) [IsOpenImmersion ι]
    (w : h ≫ g = f) :
    openInverseImageMap f g h ι w ≫ openInverseImageι g ι =
      openInverseImageι f ι ≫ h :=
  sorry

/-- `openInverseImageMap` commutes with the comparisons to `V`. -/
theorem openInverseImageMap_to {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) (h : X ⟶ Z) (ι : V ⟶ Y) [IsOpenImmersion ι]
    (w : h ≫ g = f) :
    openInverseImageMap f g h ι w ≫ openInverseImageTo g ι =
      openInverseImageTo f ι :=
  sorry

/-- Reassociates a right-associated factorization identity into the composite
required by `openInverseImageMap`. -/
theorem openInverseImageMap_factor {S : Scheme.{u}} {X Y Z W : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Z ⟶ Y} {h₁ : X ⟶ W} {h₂ : W ⟶ Z}
    (w : h₁ ≫ h₂ ≫ g = f) : (h₁ ≫ h₂) ≫ g = f :=
  sorry

/-- A directed inverse system of finite morphisms of finite presentation into a
fixed target, together with a limit identification of a given integral morphism
with the cone vertex over the target, such that each comparison of inverse
images of a given open immersion is an isomorphism. -/
structure IntegralFiniteApproximationOverOpen {S : Scheme.{u}}
    {X Y V : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (ι : V ⟶ Y) [IsOpenImmersion ι] where
  /-- The directed index type of the approximating inverse system. -/
  I : Type u
  /-- The preorder on the index type of the approximating inverse system. -/
  [preorderI : Preorder I]
  /-- The approximating inverse system has at least one stage. -/
  [nonemptyI : Nonempty I]
  /-- Any two stages of the approximating inverse system admit a common later stage. -/
  [directedI : IsDirected I (· ≤ ·)]
  /-- The inverse system of approximating algebraic spaces over `S`. -/
  D : OrderDual I ⥤ AlgebraicSpace S
  /-- The structure morphisms of the approximating stages over `Y`. -/
  σ : D ⟶ (Functor.const (OrderDual I)).obj Y
  /-- A cone from the approximating inverse system. -/
  c : Cone D
  /-- The cone is a limit cone. -/
  isLimit : IsLimit c
  /-- The identification of `X` with the vertex of the limit cone. -/
  iso : X ≅ c.pt
  /-- After identifying `X` with the cone vertex, the cone legs recover `f` over `Y`. -/
  over_lim : ∀ i, iso.hom ≫ c.π.app i ≫ σ.app i = f
  /-- Every approximating stage is finite over `Y`. -/
  stageFinite : ∀ i, IsFinite (σ.app i)
  /-- Every approximating stage is of finite presentation over `Y`. -/
  stageFinitePresentation : ∀ i, FinitePresentation (σ.app i)
  /-- Each comparison `f⁻¹V ⟶ Xᵢ⁻¹V` is an isomorphism. -/
  stageInverseImageIso :
    ∀ i, IsIso (openInverseImageMap f (σ.app i) (iso.hom ≫ c.π.app i) ι
      (openInverseImageMap_factor (over_lim i)))

namespace IntegralFiniteApproximationOverOpen

/-- Package a directed inverse system of finite morphisms of finite presentation
into `Y`, together with a limit identification recovering `f` and stagewise
isomorphisms of inverse images of `ι`. -/
def of {S : Scheme.{u}} {X Y V : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] (ι : V ⟶ Y) [IsOpenImmersion ι]
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (σ : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (isLimit : IsLimit c) (iso : X ≅ c.pt)
    (over_lim : ∀ i, iso.hom ≫ c.π.app i ≫ σ.app i = f)
    (stageFinite : ∀ i, IsFinite (σ.app i))
    (stageFinitePresentation : ∀ i, FinitePresentation (σ.app i))
    (stageInverseImageIso :
      ∀ i, IsIso (openInverseImageMap f (σ.app i) (iso.hom ≫ c.π.app i) ι
        (openInverseImageMap_factor (over_lim i)))) :
    IntegralFiniteApproximationOverOpen f ι where
  I := I
  D := D
  σ := σ
  c := c
  isLimit := isLimit
  iso := iso
  over_lim := over_lim
  stageFinite := stageFinite
  stageFinitePresentation := stageFinitePresentation
  stageInverseImageIso := stageInverseImageIso

/-- An integral finite approximation over an open recovers `f` over `Y`, with
finite morphisms of finite presentation as stages, and with inverse-image
comparisons of `ι` isomorphic at every stage. -/
theorem spec {S : Scheme.{u}} {X Y V : AlgebraicSpace S} {f : X ⟶ Y}
    [IsIntegralHom f] {ι : V ⟶ Y} [IsOpenImmersion ι]
    (A : IntegralFiniteApproximationOverOpen f ι) :
    -- Local instance justification (defeq pin): `A.D` and `homOfLE` are typed using the stored `A.preorderI`.
    letI := A.preorderI
    (∀ i, A.iso.hom ≫ A.c.π.app i ≫ A.σ.app i = f) ∧
      (∀ i, IsFinite (A.σ.app i)) ∧
      (∀ i, FinitePresentation (A.σ.app i)) ∧
      ∀ i, IsIso (openInverseImageMap f (A.σ.app i) (A.iso.hom ≫ A.c.π.app i) ι
        (openInverseImageMap_factor (A.over_lim i))) :=
  sorry

/-- Forget the inverse-image isomorphism condition, recovering an unrefined
integral finite approximation. -/
def toIntegralFiniteApproximation {S : Scheme.{u}} {X Y V : AlgebraicSpace S}
    {f : X ⟶ Y} [IsIntegralHom f] {ι : V ⟶ Y} [IsOpenImmersion ι]
    (A : IntegralFiniteApproximationOverOpen f ι) :
    IntegralFiniteApproximation f where
  I := A.I
  preorderI := A.preorderI
  nonemptyI := A.nonemptyI
  directedI := A.directedI
  D := A.D
  σ := A.σ
  c := A.c
  isLimit := A.isLimit
  iso := A.iso
  over_lim := A.over_lim
  stageFinite := A.stageFinite
  stageFinitePresentation := A.stageFinitePresentation

end IntegralFiniteApproximationOverOpen

/-- An integral morphism of algebraic spaces over a scheme, with quasi-compact
quasi-separated target, and a quasi-compact open immersion into the target
whose inverse image is finite and of finite presentation, admits a directed
inverse system of finite morphisms of finite presentation into the target whose
limit is identified with the source and whose inverse images of the open are
stagewise isomorphic. -/
theorem exists_integralFiniteApproximationOverOpen
    {S : Scheme.{u}} {X Y V : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (ι : V ⟶ Y) [IsOpenImmersion ι] [QuasiCompact ι]
    [IsFinite (openInverseImageTo f ι)]
    [FinitePresentation (openInverseImageTo f ι)] :
    Nonempty (IntegralFiniteApproximationOverOpen f ι) :=
  sorry

/-- Integral finite approximation over an open is equivalent to the existence of
a directed inverse system with finite morphisms of finite presentation as
stages over the target, a limit identification of the source recovering the
morphism, and stagewise isomorphisms of inverse images of the open. -/
theorem exists_integralFiniteApproximationOverOpen_nonempty_iff
    {S : Scheme.{u}} {X Y V : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (ι : V ⟶ Y) [IsOpenImmersion ι] [QuasiCompact ι]
    [IsFinite (openInverseImageTo f ι)]
    [FinitePresentation (openInverseImageTo f ι)] :
    Nonempty (IntegralFiniteApproximationOverOpen f ι) ↔
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : OrderDual I ⥤ AlgebraicSpace S)
        (σ : D ⟶ (Functor.const (OrderDual I)).obj Y) (c : Cone D)
        (_ : IsLimit c) (iso : X ≅ c.pt)
        (over_lim : ∀ i, iso.hom ≫ c.π.app i ≫ σ.app i = f)
        (_ : ∀ i, IsFinite (σ.app i))
        (_ : ∀ i, FinitePresentation (σ.app i)),
        ∀ i, IsIso (openInverseImageMap f (σ.app i) (iso.hom ≫ c.π.app i) ι
          (openInverseImageMap_factor (over_lim i))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
