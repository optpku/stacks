/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Extension of the base of algebraic spaces

For a morphism `g : S ⟶ S'`, extend a functor of points by taking the coproduct
over lifts of each test scheme's structure morphism through `g`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of schemes over `S'` induces a morphism over `S` after choosing
a lift of its target's structure morphism through `g : S ⟶ S'`. -/
def restrictIndex {S S' : Scheme.{u}} {T' T'' : Over S'} {g : S ⟶ S'}
    (f : T'' ⟶ T') (φ : T' ⟶ Over.mk g) :
    Over.mk (f ≫ φ).left ⟶ Over.mk φ.left :=
  Over.homMk f.left

/-- Extension along `g : S ⟶ S'` sends a presheaf `F` to the presheaf whose
sections on `T'` are a lift `φ : T' ⟶ Over.mk g` and a section of `F` on
`T'` viewed over `S` through `φ`. -/
def extendBasePresheaf {S S' : Scheme.{u}} (g : S ⟶ S') (F : (Over S)ᵒᵖ ⥤ Type u) :
    (Over S')ᵒᵖ ⥤ Type u :=
  let obj := fun T' : (Over S')ᵒᵖ ↦
    Σ φ : T'.unop ⟶ Over.mk g, F.obj (op (Over.mk φ.left))
  let map : ∀ {T' T'' : (Over S')ᵒᵖ}, (T' ⟶ T'') → (obj T' ⟶ obj T'') :=
    fun f ↦ ofHom fun σ ↦
      ⟨f.unop ≫ σ.1, F.map (restrictIndex f.unop σ.1).op σ.2⟩
  let laws : (∀ T', map (𝟙 T') = 𝟙 (obj T')) ∧
      (∀ {T' T'' T''' : (Over S')ᵒᵖ} (f : T' ⟶ T'') (h : T'' ⟶ T'''),
        map (f ≫ h) = map f ≫ map h) := sorry
  { obj := obj, map := map, map_id := laws.1, map_comp := laws.2 }

/-- Extension along a morphism of base schemes preserves the fppf sheaf condition. -/
theorem isSheaf_extendBasePresheaf {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : (Over S)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S') (extendBasePresheaf g F) := sorry

/-- View an algebraic space over `S` as an algebraic space over `S'` along
`g : S ⟶ S'`, using the coproduct extension of its functor of points. -/
def extendBase {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    AlgebraicSpace S' :=
  let presheaf := extendBasePresheaf g F.functorOfPoints
  let laws : yoneda.relativelyRepresentable (Limits.diag presheaf) ∧
      (∃ (U : Over S') (p : yoneda.obj U ⟶ presheaf),
        MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S') p) := sorry
  ofFunctor presheaf (isSheaf_extendBasePresheaf g F.functorOfPoints F.isSheaf)
    laws.1 laws.2

end AlgebraicGeometry.AlgebraicSpace
