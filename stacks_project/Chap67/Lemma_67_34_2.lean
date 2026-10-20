module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg.Composition

/-!
# Additivity of relative dimensions for morphisms of algebraic spaces

Relative dimension at a point is subadditive under composition of locally
finite-type morphisms of algebraic spaces, and is additive when the induced
map of fibres over a field-valued point is flat. Residue-field transcendence
degree is additive without a flatness hypothesis.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.34.2 (1): Let `S` be a scheme and let `f : X ⟶ Y` and `g : Y ⟶ Z`
be morphisms of algebraic spaces over `S`, both locally of finite type. If `f`
has relative dimension `d` at a point `x` of `X` and `g` has relative dimension
`e` at `Points.map f x`, then `f ≫ g` has relative dimension at most `d + e`
at `x`. -/
@[stacks 04NR] #check
  (AlgebraicGeometry.AlgebraicSpace.relativeDimensionLEAt_comp_add :
    ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (d e : ℕ) (x : Points X)
    (hd : RelativeDimensionAt f d x)
    (he : RelativeDimensionAt g e (Points.map f x)),
    RelativeDimensionLEAt (f ≫ g) (d + e) x)

/- Lemma 67.34.2 (2): In the same setting, `f ≫ g` has relative dimension
exactly `d + e` at `x` if for some morphism `Spec(k) ⟶ Z` from the spectrum of
a field in the class of `Points.map (f ≫ g) x` the induced map `X_k ⟶ Y_k` of
fibres is flat at a point of `X_k` lifting `x`. -/
@[stacks 04NR] #check
  (AlgebraicGeometry.AlgebraicSpace.relativeDimensionAt_comp_add_of_flatAt_compFiberToBaseFiber :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (d e : ℕ) (x : Points X)
    (hd : RelativeDimensionAt f d x)
    (he : RelativeDimensionAt g e (Points.map f x))
    (p : FieldValuedPoint Z) (hp : Points.mk p = Points.map (f ≫ g) x)
    (x' : Points (pullbackAlongScheme (f ≫ g) p.hom))
    (hx' : Points.map (pullbackAlongScheme.fst (f ≫ g) p.hom) x' = x)
    (hflat : FlatAt (compFiberToBaseFiber f g p) x'),
    RelativeDimensionAt (f ≫ g) (d + e) x)

/- Equality in Lemma 67.34.2 (1) also holds if `f` itself is flat at `x`. -/
@[stacks 04NR] #check
  (AlgebraicGeometry.AlgebraicSpace.relativeDimensionAt_comp_add_of_flatAt :
    ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (d e : ℕ) (x : Points X)
    (hd : RelativeDimensionAt f d x)
    (he : RelativeDimensionAt g e (Points.map f x)) (hflat : FlatAt f x),
    RelativeDimensionAt (f ≫ g) (d + e) x)

/- Lemma 67.34.2 (3): In the same setting, the residue-field transcendence
degree of `x` over `Points.map (f ≫ g) x` equals the sum of the residue-field
transcendence degree of `x` over `Points.map f x` and that of `Points.map f x`
over `Points.map (f ≫ g) x`. -/
@[stacks 04NR] #check
  (AlgebraicGeometry.AlgebraicSpace.residueFieldTrdegAt.comp_eq :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (x : Points X),
    residueFieldTrdegAt (f ≫ g) x =
      residueFieldTrdegAt f x + residueFieldTrdegAt g (Points.map f x))

end AlgebraicGeometry.AlgebraicSpace
