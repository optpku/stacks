module

public import ReasLib.AlgebraicGeometry.Correspondence.Graph
public import ReasLib.AlgebraicGeometry.Correspondence.Chow
public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- The covariant graph map is proper when its target is separated over the field. -/
instance covariantGraphMap_isProper {X Y : SchemeOverField k} [IsSeparated Y.hom]
    (f : X ⟶ Y) : IsProper (Limits.prod.lift (𝟙 X) f).left := sorry

/-- The integral covariant graph correspondence of a flat morphism of relative dimension
`r`, obtained by pushing its flat-pullback class along its graph. -/
def integralFlatGraph {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y) (r : ℕ)
    [Flat f.left] [Scheme.Hom.RelativeDimension f.left r] :
    Integral X Y (-(r : ℤ)) :=
  BivariantClass.properPushforward (fun _ ↦ 0) (Limits.prod.lift (𝟙 X) f)
    Limits.prod.snd (-(r : ℤ))
    (castHom (Limits.prod.lift_snd (𝟙 X) f).symm (-(r : ℤ))
      (BivariantClass.flatPullback (fun _ ↦ 0) f r))

/-- The rational covariant graph correspondence of a flat morphism. -/
def rationalFlatGraph {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y) (r : ℕ)
    [Flat f.left] [Scheme.Hom.RelativeDimension f.left r] :
    Rational X Y (-(r : ℤ)) :=
  BivariantClass.rationalize (fun _ ↦ 0) Limits.prod.snd (-(r : ℤ))
    (integralFlatGraph f r)

/-- Every nonempty fibre of an open immersion has dimension zero. -/
theorem openImmersion_relativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : Scheme.Hom.RelativeDimension f 0 := sorry

/-- The covariant graph of an open immersion, of correspondence degree zero. -/
def rationalOpenGraph {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)
    [IsOpenImmersion f.left] : Rational X Y 0 :=
  @rationalFlatGraph k _ X Y _ _ _ f 0 inferInstance
    (openImmersion_relativeDimension f.left)

/-- The graph of an open immersion is the rationalized flat graph in relative dimension zero. -/
theorem rationalOpenGraph_def {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)
    [IsOpenImmersion f.left] :
    rationalOpenGraph f =
      @rationalFlatGraph k _ X Y _ _ _ f 0 inferInstance
        (openImmersion_relativeDimension f.left) := rfl

end AlgebraicGeometry.Correspondence
