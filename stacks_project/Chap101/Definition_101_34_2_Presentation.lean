/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_12_2_Etale

/-!
# Mixed étale-smooth algebraic-space presentation squares

A DM morphism of algebraic stacks may be tested on 2-commutative squares whose
vertices are algebraic spaces, whose target atlas `V ⟶ Y` is smooth, and whose
comparison into the 2-fibre product `TwoFibreProduct.apex f b` is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A 2-commutative square presenting a morphism of algebraic stacks by algebraic
spaces, with smooth target atlas `b : V.toGroupoids ⟶ Y`. -/
def IsEtaleSmoothSpaceSquare {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) : Prop :=
  Groupoids.Hom.Smooth b ∧
    Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b)

/-- A square is an étale-smooth algebraic-space presentation square if and only
if the target atlas is smooth and the two paths `U.toGroupoids ⟶ Y` are
2-isomorphic. -/
theorem IsEtaleSmoothSpaceSquare.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) :
    IsEtaleSmoothSpaceSquare f a b h ↔
      Groupoids.Hom.Smooth b ∧
        Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b) :=
  sorry

/-- A smooth target atlas and a 2-isomorphism of paths yield an étale-smooth
algebraic-space presentation square. -/
theorem IsEtaleSmoothSpaceSquare.of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V} (hb : Groupoids.Hom.Smooth b)
    (hsq : Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b)) :
    IsEtaleSmoothSpaceSquare f a b h :=
  sorry

/-- An étale-smooth algebraic-space presentation square has a smooth target
atlas and a 2-isomorphism of the two paths `U.toGroupoids ⟶ Y`. -/
theorem IsEtaleSmoothSpaceSquare.spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (hsq : IsEtaleSmoothSpaceSquare f a b h) :
    Groupoids.Hom.Smooth b ∧
      Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b) :=
  sorry

/-- The comparison `U ⟶ X ×_Y V` is étale: some 1-morphism to the chosen
2-fibre product `TwoFibreProduct.apex f b` is étale and 2-isomorphic to the
given legs `a` and `toGroupoids.map h`. -/
def HasEtaleComparison {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) : Prop :=
  ∃ φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b,
    Groupoids.Hom.Etale φ ∧
      Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a) ∧
        Nonempty
          (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
            AlgebraicSpace.toGroupoids.map h)

/-- Étale comparison into `TwoFibreProduct.apex f b` means some étale 1-morphism
is 2-isomorphic to the given legs. -/
theorem HasEtaleComparison.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) :
    HasEtaleComparison f a b h ↔
      ∃ φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b,
        Groupoids.Hom.Etale φ ∧
          Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a) ∧
            Nonempty
              (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
                AlgebraicSpace.toGroupoids.map h) :=
  sorry

/-- An étale comparison 1-morphism into `TwoFibreProduct.apex f b` witnesses
`HasEtaleComparison`. -/
theorem HasEtaleComparison.of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b)
    (hφ : Groupoids.Hom.Etale φ)
    (hfst : Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a))
    (hsnd : Nonempty
      (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
        AlgebraicSpace.toGroupoids.map h)) :
    HasEtaleComparison f a b h :=
  sorry

/-- An étale comparison supplies a 1-morphism `φ` to `TwoFibreProduct.apex f b`
that is étale and 2-isomorphic to the given legs. -/
theorem HasEtaleComparison.spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V} (hφ : HasEtaleComparison f a b h) :
    ∃ φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b,
      Groupoids.Hom.Etale φ ∧
        Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a) ∧
          Nonempty
            (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
              AlgebraicSpace.toGroupoids.map h) :=
  sorry

/-- An étale-smooth algebraic-space presentation square whose source atlas is
surjective and whose comparison into `TwoFibreProduct.apex f b` is étale. -/
def IsEtaleSmoothSurjectivePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) : Prop :=
  IsEtaleSmoothSpaceSquare f a b h ∧ HasEtaleComparison f a b h ∧
    Groupoids.Hom.Surjective a

/-- A square is an étale-smooth surjective presentation if and only if it is an
étale-smooth algebraic-space square with étale comparison and surjective source
atlas. -/
theorem IsEtaleSmoothSurjectivePresentation.iff {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {U V : AlgebraicSpace S} (f : X ⟶ Y)
    (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) :
    IsEtaleSmoothSurjectivePresentation f a b h ↔
      IsEtaleSmoothSpaceSquare f a b h ∧ HasEtaleComparison f a b h ∧
        Groupoids.Hom.Surjective a :=
  sorry

/-- An étale-smooth algebraic-space square with étale comparison and surjective
source atlas is an étale-smooth surjective presentation. -/
theorem IsEtaleSmoothSurjectivePresentation.of {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {U V : AlgebraicSpace S} {f : X ⟶ Y}
    {a : U.toGroupoids ⟶ X} {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (hsq : IsEtaleSmoothSpaceSquare f a b h) (hφ : HasEtaleComparison f a b h)
    (ha : Groupoids.Hom.Surjective a) :
    IsEtaleSmoothSurjectivePresentation f a b h :=
  sorry

/-- An étale-smooth surjective presentation is an étale-smooth algebraic-space
square with étale comparison and surjective source atlas. -/
theorem IsEtaleSmoothSurjectivePresentation.spec {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {U V : AlgebraicSpace S} {f : X ⟶ Y}
    {a : U.toGroupoids ⟶ X} {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (hpres : IsEtaleSmoothSurjectivePresentation f a b h) :
    IsEtaleSmoothSpaceSquare f a b h ∧ HasEtaleComparison f a b h ∧
      Groupoids.Hom.Surjective a :=
  sorry

/-- Every 2-commutative algebraic-space square over `f` with smooth target atlas
and étale comparison into `TwoFibreProduct.apex f b` has `P` on the top
arrow. -/
def forallEtaleSmoothComparison {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) : Prop :=
  ∀ {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
    (h : U ⟶ V),
    IsEtaleSmoothSpaceSquare f a b h → HasEtaleComparison f a b h → P h

/-- `forallEtaleSmoothComparison P f` means `P` holds on the top arrow of every
étale-smooth algebraic-space square over `f` with étale comparison. -/
theorem forallEtaleSmoothComparison.iff {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    forallEtaleSmoothComparison P f ↔
      ∀ {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsEtaleSmoothSpaceSquare f a b h → HasEtaleComparison f a b h → P h :=
  sorry

/-- The universal checking condition yields `forallEtaleSmoothComparison`. -/
theorem forallEtaleSmoothComparison.of {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    {f : X ⟶ Y}
    (hP : ∀ {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X)
      (b : V.toGroupoids ⟶ Y) (h : U ⟶ V),
      IsEtaleSmoothSpaceSquare f a b h → HasEtaleComparison f a b h → P h) :
    forallEtaleSmoothComparison P f :=
  sorry

/-- Under `forallEtaleSmoothComparison`, the top arrow of an étale-smooth
algebraic-space square with étale comparison has `P`. -/
theorem forallEtaleSmoothComparison.spec {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    {f : X ⟶ Y} (hf : forallEtaleSmoothComparison P f) {U V : AlgebraicSpace S}
    (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y) (h : U ⟶ V)
    (hsq : IsEtaleSmoothSpaceSquare f a b h) (hφ : HasEtaleComparison f a b h) :
    P h :=
  sorry

/-- Some étale-smooth algebraic-space square over `f` with étale comparison and
surjective source atlas has `P` on the top arrow. -/
def existsSurjectiveEtaleSmoothSquare {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
    (h : U ⟶ V), IsEtaleSmoothSurjectivePresentation f a b h ∧ P h

/-- `existsSurjectiveEtaleSmoothSquare P f` is the existence of an étale-smooth
surjective algebraic-space presentation whose top arrow has `P`. -/
theorem existsSurjectiveEtaleSmoothSquare.iff {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    existsSurjectiveEtaleSmoothSquare P f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V), IsEtaleSmoothSurjectivePresentation f a b h ∧ P h :=
  sorry

/-- An étale-smooth surjective presentation whose top arrow has `P` witnesses
`existsSurjectiveEtaleSmoothSquare`. -/
theorem existsSurjectiveEtaleSmoothSquare.of {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    {f : X ⟶ Y} {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V)
    (hpres : IsEtaleSmoothSurjectivePresentation f a b h) (hP : P h) :
    existsSurjectiveEtaleSmoothSquare P f :=
  sorry

/-- A witness of `existsSurjectiveEtaleSmoothSquare` supplies an étale-smooth
surjective presentation whose top arrow has `P`. -/
theorem existsSurjectiveEtaleSmoothSquare.spec {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    {f : X ⟶ Y} (hf : existsSurjectiveEtaleSmoothSquare P f) :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V), IsEtaleSmoothSurjectivePresentation f a b h ∧ P h :=
  sorry

end AlgebraicGeometry.AlgebraicStack
