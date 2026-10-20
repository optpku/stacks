module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothPresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat

/-!
# Flat morphisms of algebraic stacks

Flatness is characterized by smooth algebraic-space presentation squares with
surjective source atlas and flat top arrow. For morphisms representable by
algebraic spaces, it agrees with representable flatness.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks over `S` is flat if some
commutative square with algebraic-space vertices, smooth vertical arrows, and
surjective source atlas has flat top arrow. -/
class Flat {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- There is a smooth presentation of `f` by algebraic spaces whose source
  atlas is surjective and whose top arrow is flat. -/
  exists_surjective_smooth_presentation :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Flat h

/-- A morphism of algebraic stacks is flat if and only if it admits a smooth
algebraic-space presentation with surjective source atlas and flat top
arrow. -/
theorem flat_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Flat f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Flat h :=
  sorry

namespace Flat

/-- The identity morphism of an algebraic stack is flat. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Flat (𝟙 X) :=
  sorry

/-- A flat morphism of algebraic stacks admits a smooth algebraic-space
presentation with surjective source atlas and flat top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f] :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Flat h :=
  sorry

/-- A 1-morphism of algebraic stacks which is flat in the sense of relative
representability by algebraic spaces is flat as a morphism of algebraic
stacks. -/
instance of_groupoidsHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Flat f] : Flat f :=
  sorry

/-- For a morphism of algebraic stacks representable by algebraic spaces,
flatness in the sense of algebraic stacks agrees with relative-representable
flatness. -/
theorem iff_groupoidsHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    Flat f ↔ Groupoids.Hom.Flat f :=
  sorry

/-- If `f` is flat, then every smooth algebraic-space square over `f` whose
comparison morphism to the 2-fibre product is smooth has flat top arrow. -/
theorem of_smooth_square {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f]
    {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
    (h : U ⟶ V)
    (φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} b f)
    (ha : Groupoids.Hom.Smooth a) (hb : Groupoids.Hom.Smooth b)
    (hφ : Groupoids.Hom.Smooth φ)
    (hfst : Nonempty
      (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} b f ≅
        AlgebraicSpace.toGroupoids.map h))
    (hsnd : Nonempty
      (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} b f ≅ a)) :
    AlgebraicSpace.Flat h :=
  sorry

end Flat

end AlgebraicGeometry.AlgebraicStack
