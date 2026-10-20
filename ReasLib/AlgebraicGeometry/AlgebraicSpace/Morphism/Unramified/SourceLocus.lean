module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Cancellation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Unramified source loci and arbitrary base change

The points where a morphism of algebraic spaces is unramified form a canonical
open subspace. For locally finite-type morphisms, this locus commutes with
arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Unramified

/-- The set of points at which `f` is unramified is open in `Points X`. -/
theorem isOpen_unramifiedAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : IsOpen (setOf (UnramifiedAt f)) :=
  sorry

/-- The open subspace of the source consisting of the points where the morphism
is unramified. -/
abbrev sourceLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    OpenSubspace X :=
  let W : Opens (Points X) := ⟨{x | UnramifiedAt f x}, isOpen_unramifiedAt f⟩
  { X := OpenSubspace.Construction.space X W
    ι := OpenSubspace.Construction.ι X W
    isOpenImmersion := OpenSubspace.Construction.inclusion_isOpenImmersion X W }

/-- The restriction of `f` to its unramified source locus is unramified. -/
instance sourceLocus_unramified {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Unramified ((sourceLocus f).ι ≫ f) :=
  sorry

/-- The points of the unramified source locus of `f` are exactly the points at
which `f` is unramified. -/
theorem sourceLocus_pointsSet_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (sourceLocus f).pointsSet = {x | UnramifiedAt f x} :=
  OpenSubspace.fromOpens_pointsSet
    (⟨{x | UnramifiedAt f x}, isOpen_unramifiedAt f⟩ : Opens (Points X))

/-- A point of `X` lies in the unramified source locus of `f` if and only if `f`
is unramified at that point. -/
theorem mem_sourceLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    x ∈ (sourceLocus f).pointsSet ↔ UnramifiedAt f x :=
  by rw [sourceLocus_pointsSet_eq]; rfl

/-- Any open immersion along which `f` is unramified factors through the
unramified source locus on points. -/
theorem sourceLocus_maximal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U : AlgebraicSpace S} (i : U ⟶ X) [IsOpenImmersion i]
    (hf : Unramified (i ≫ f)) :
    Set.range (Points.map i) ⊆ (sourceLocus f).pointsSet :=
  sorry

/-- The base change of `f : X ⟶ Y` over `Z` along `g : Z' ⟶ Z`, as the
comparison `X ×_Z Z' ⟶ Y ×_Z Z'`. -/
def overBaseChange {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z) :
    pullback (f ≫ q) g ⟶ pullback q g :=
  pullback.map (f ≫ q) g q g f (𝟙 Z') (𝟙 Z)
    (Category.comp_id (f ≫ q)) (by simp only [Category.comp_id, Category.id_comp])

/-- The first projection identity for `overBaseChange`. -/
theorem overBaseChange_fst {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z) :
    overBaseChange f q g ≫ pullback.fst q g =
      pullback.fst (f ≫ q) g ≫ f :=
  sorry

/-- The second projection identity for `overBaseChange`. -/
theorem overBaseChange_snd {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z) :
    overBaseChange f q g ≫ pullback.snd q g =
      pullback.snd (f ≫ q) g :=
  sorry

/-- In a cartesian square of algebraic spaces, pointwise unramifiedness is
preserved and reflected when the original morphism is locally of finite type. -/
theorem unramifiedAt_iff_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (x' : Points X') :
    UnramifiedAt f' x' ↔ UnramifiedAt f (Points.map g' x') :=
  sorry

/-- In a cartesian square of algebraic spaces, the unramified source locus of the
base-changed morphism is the preimage of the original unramified source locus. -/
theorem sourceLocus_eq_preimage_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f] :
    (sourceLocus f').pointsSet = Points.map g' ⁻¹' (sourceLocus f).pointsSet :=
  sorry

/-- The unramified source locus of a canonical pullback projection is the
preimage of the unramified source locus along the other projection. -/
theorem sourceLocus_pullback_snd {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y' ⟶ Y) :
    (sourceLocus (pullback.snd f g)).pointsSet =
      Points.map (pullback.fst f g) ⁻¹' (sourceLocus f).pointsSet :=
  sorry

end Unramified

/-- For a triangle with locally finite-type composite, the unramified source
locus commutes with arbitrary base change of the base. -/
theorem unramified_sourceLocus_eq_preimage_of_over_baseChange
    {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] :
    (Unramified.sourceLocus (Unramified.overBaseChange f q g)).pointsSet =
      Points.map (pullback.fst (f ≫ q) g) ⁻¹'
        (Unramified.sourceLocus f).pointsSet :=
  sorry

/-- The unramified source locus is a largest open source subspace on which `f`
is unramified. -/
theorem isLargestSourceOpen_unramified_sourceLocus {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    (Unramified ((Unramified.sourceLocus f).ι ≫ f) ∧
      ∀ U : OpenSubspace X, Unramified (U.ι ≫ f) →
        U.pointsSet ⊆ (Unramified.sourceLocus f).pointsSet) :=
  sorry

/-- A locally finite-type morphism of algebraic spaces has a largest open source
subspace on which its restriction is unramified. -/
theorem exists_isLargestSourceOpen_unramified {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    ∃ W : OpenSubspace X, (Unramified (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Unramified (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet) :=
  sorry

/-- The largest open source subspace on which `f` is unramified is stable under
arbitrary base change. -/
theorem isLargestSourceOpen_unramified_pullback {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyOfFiniteType f] (W : OpenSubspace X)
    (hW : (Unramified (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Unramified (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet)) :
    (Unramified ((W.inverseImage (pullback.fst f g)).ι ≫ (pullback.snd f g)) ∧
      ∀ U : OpenSubspace (pullback f g), Unramified (U.ι ≫ (pullback.snd f g)) →
        U.pointsSet ⊆ (W.inverseImage (pullback.fst f g)).pointsSet) :=
  sorry

/-- If `W` is a largest open source subspace on which `f` is unramified, then
the points of `W` are exactly the points at which `f` is unramified. -/
theorem isLargestSourceOpen_unramified_pointsSet {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (W : OpenSubspace X) (hW : (Unramified (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Unramified (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet)) :
    W.pointsSet = {x | UnramifiedAt f x} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
