module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Lemma_100_7_4_Points
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Flat algebraic-space squares through a point

A morphism of algebraic stacks may be tested for flatness at a source point on
2-commutative algebraic-space squares whose target atlas is flat and whose
comparison into the 2-fibre product `TwoFibreProduct.apex f b` is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The comparison `U ⟶ X ×_Y V` is flat: some 1-morphism to the chosen
2-fibre product `TwoFibreProduct.apex f b` is flat and 2-isomorphic to the
given legs `a` and `toGroupoids.map h`. -/
def HasFlatComparison {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) : Prop :=
  ∃ φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b,
    Groupoids.Hom.Flat φ ∧
      Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a) ∧
        Nonempty
          (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
            AlgebraicSpace.toGroupoids.map h)

/-- Flat comparison into `TwoFibreProduct.apex f b` means some flat 1-morphism
is 2-isomorphic to the given legs. -/
theorem HasFlatComparison.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) :
    HasFlatComparison f a b h ↔
      ∃ φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b,
        Groupoids.Hom.Flat φ ∧
          Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a) ∧
            Nonempty
              (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
                AlgebraicSpace.toGroupoids.map h) :=
  sorry

/-- A flat comparison 1-morphism into `TwoFibreProduct.apex f b` witnesses
`HasFlatComparison`. -/
theorem HasFlatComparison.of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b)
    (hφ : Groupoids.Hom.Flat φ)
    (hfst : Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a))
    (hsnd : Nonempty
      (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
        AlgebraicSpace.toGroupoids.map h)) :
    HasFlatComparison f a b h :=
  sorry

/-- A flat comparison supplies a 1-morphism `φ` to `TwoFibreProduct.apex f b`
that is flat and 2-isomorphic to the given legs. -/
theorem HasFlatComparison.spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V} (hφ : HasFlatComparison f a b h) :
    ∃ φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b,
      Groupoids.Hom.Flat φ ∧
        Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a) ∧
          Nonempty
            (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
              AlgebraicSpace.toGroupoids.map h) :=
  sorry

/-- A 2-commutative algebraic-space square over `f` whose target atlas `b` is
flat and whose comparison into `TwoFibreProduct.apex f b` is flat. -/
def IsFlatAtPointSquare {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) : Prop :=
  Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b) ∧
    Groupoids.Hom.Flat b ∧ HasFlatComparison f a b h

/-- A square is an `IsFlatAtPointSquare` if and only if it 2-commutes, the
target atlas is flat, and the comparison into `TwoFibreProduct.apex f b` is
flat. -/
theorem IsFlatAtPointSquare.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) :
    IsFlatAtPointSquare f a b h ↔
      Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b) ∧
        Groupoids.Hom.Flat b ∧ HasFlatComparison f a b h :=
  sorry

/-- A 2-commutative square with flat target atlas and flat comparison is an
`IsFlatAtPointSquare`. -/
theorem IsFlatAtPointSquare.of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (hsq : Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b))
    (hb : Groupoids.Hom.Flat b) (hφ : HasFlatComparison f a b h) :
    IsFlatAtPointSquare f a b h :=
  sorry

/-- An `IsFlatAtPointSquare` 2-commutes, has flat target atlas, and has flat
comparison into `TwoFibreProduct.apex f b`. -/
theorem IsFlatAtPointSquare.spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V} (hsq : IsFlatAtPointSquare f a b h) :
    Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b) ∧
      Groupoids.Hom.Flat b ∧ HasFlatComparison f a b h :=
  sorry

/-- There exists a 2-commutative algebraic-space square over `f` through `x`
with flat target atlas, flat comparison, and top arrow flat at the chosen
point of `U`. -/
def existsFlatAtPointSquare {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : Points X) : Prop :=
  ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
    (h : U ⟶ V) (u : AlgebraicSpace.Points U),
    IsFlatAtPointSquare f a b h ∧ Points.mapSpace a u = x ∧
      AlgebraicSpace.FlatAt h u

/-- `existsFlatAtPointSquare f x` is the existence of a flat-at-a-point test
square through `x` whose top arrow is flat at the chosen point of `U`. -/
theorem existsFlatAtPointSquare.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : Points X) :
    existsFlatAtPointSquare f x ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V) (u : AlgebraicSpace.Points U),
        IsFlatAtPointSquare f a b h ∧ Points.mapSpace a u = x ∧
          AlgebraicSpace.FlatAt h u :=
  sorry

/-- A flat-at-a-point test square through `x` whose top arrow is flat at `u`
witnesses `existsFlatAtPointSquare`. -/
theorem existsFlatAtPointSquare.of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {x : Points X}
    {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
    (h : U ⟶ V) (u : AlgebraicSpace.Points U)
    (hsq : IsFlatAtPointSquare f a b h) (hx : Points.mapSpace a u = x)
    (hh : AlgebraicSpace.FlatAt h u) : existsFlatAtPointSquare f x :=
  sorry

/-- A witness of `existsFlatAtPointSquare` supplies a flat-at-a-point test
square through `x` whose top arrow is flat at the chosen point of `U`. -/
theorem existsFlatAtPointSquare.spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {x : Points X}
    (hf : existsFlatAtPointSquare f x) :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V) (u : AlgebraicSpace.Points U),
      IsFlatAtPointSquare f a b h ∧ Points.mapSpace a u = x ∧
        AlgebraicSpace.FlatAt h u :=
  sorry

/-- Every 2-commutative algebraic-space square over `f` through `x` with flat
target atlas and flat comparison has top arrow flat at the chosen point of
`U`. -/
def forallFlatAtPointSquare {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : Points X) : Prop :=
  ∀ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
    (h : U ⟶ V) (u : AlgebraicSpace.Points U),
    IsFlatAtPointSquare f a b h → Points.mapSpace a u = x →
      AlgebraicSpace.FlatAt h u

/-- `forallFlatAtPointSquare f x` means the top arrow of every flat-at-a-point
test square through `x` is flat at the chosen point of `U`. -/
theorem forallFlatAtPointSquare.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (x : Points X) :
    forallFlatAtPointSquare f x ↔
      ∀ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V) (u : AlgebraicSpace.Points U),
        IsFlatAtPointSquare f a b h → Points.mapSpace a u = x →
          AlgebraicSpace.FlatAt h u :=
  sorry

/-- The universal flat-at-a-point square condition yields
`forallFlatAtPointSquare`. -/
theorem forallFlatAtPointSquare.of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {x : Points X}
    (hP : ∀ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X)
      (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) (u : AlgebraicSpace.Points U),
      IsFlatAtPointSquare f a b h → Points.mapSpace a u = x →
        AlgebraicSpace.FlatAt h u) :
    forallFlatAtPointSquare f x :=
  sorry

/-- Under `forallFlatAtPointSquare`, the top arrow of a flat-at-a-point test
square through `x` is flat at the chosen point of `U`. -/
theorem forallFlatAtPointSquare.apply {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {x : Points X}
    (hf : forallFlatAtPointSquare f x) {U V : AlgebraicSpace S}
    (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y) (h : U ⟶ V)
    (u : AlgebraicSpace.Points U) (hsq : IsFlatAtPointSquare f a b h)
    (hx : Points.mapSpace a u = x) : AlgebraicSpace.FlatAt h u :=
  sorry

end AlgebraicGeometry.AlgebraicStack
