module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.Complement

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace openComplementAlong

/-- Membership of a Yoneda section in the open complement of `T` is stable under
postcomposition with `f : X' ⟶ X`. -/
theorem mapsInto_comp {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) {U : (Over S)ᵒᵖ} {x : X'.functorOfPoints.obj U}
    (hx : Set.range (Points.map (X := ofOver U.unop) (Y := X') (yonedaEquiv.symm x)) ⊆
      ((T.preimage (Points.continuous_map f)).compl : Set (Points X'))) :
    Set.range (Points.map (X := ofOver U.unop) (Y := X) (yonedaEquiv.symm (f.app U x))) ⊆
      (T.compl : Set (Points X)) :=
  sorry

/-- The sectionwise map between complementary opens commutes with restriction. -/
theorem map_naturality {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) :
    (openComplementAlong X' (T.preimage (Points.continuous_map f))).functorOfPoints.map φ ≫
        ofHom (fun x ↦ ⟨f.app V x.1, mapsInto_comp f T x.2⟩) =
      ofHom (fun x ↦ ⟨f.app U x.1, mapsInto_comp f T x.2⟩) ≫
        (openComplementAlong X T).functorOfPoints.map φ :=
  sorry

/-- The morphism of open complements induced by `f : X' ⟶ X`, landing in the
closed preimage `T.preimage (Points.continuous_map f)`. -/
def map {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) :
    openComplementAlong X' (T.preimage (Points.continuous_map f)) ⟶
      openComplementAlong X T where
  app U := ofHom fun x ↦ ⟨f.app U x.1, mapsInto_comp f T x.2⟩
  naturality := fun _ _ φ ↦ map_naturality f T φ

/-- The underlying section of `map f T` is the component of `f`. -/
theorem map_app {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) (U : (Over S)ᵒᵖ)
    (x : (openComplementAlong X' (T.preimage (Points.continuous_map f))).functorOfPoints.obj U) :
    (openComplementι X T).app U ((map f T).app U x) =
      f.app U ((openComplementι X' (T.preimage (Points.continuous_map f))).app U x) :=
  rfl

end openComplementAlong

/-- Sections of the inverse image of a complementary open avoid the closed preimage. -/
theorem openInverseImageToOpenComplement_mem {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) (U : (Over S)ᵒᵖ)
    (p : (openInverseImage f (openComplementι X T)).functorOfPoints.obj U) :
    Set.range (Points.map (X := ofOver U.unop) (Y := X') (yonedaEquiv.symm
      ((openInverseImageι f (openComplementι X T)).app U p))) ⊆
        ((T.preimage (Points.continuous_map f)).compl : Set (Points X')) :=
  sorry

/-- The comparison from the open inverse image of `X \ T` along `f` to the open
complement of the closed preimage on `X'`. -/
def openInverseImageToOpenComplement {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) :
    openInverseImage f (openComplementι X T) ⟶
      openComplementAlong X' (T.preimage (Points.continuous_map f)) where
  app U := ofHom fun p ↦
    ⟨(openInverseImageι f (openComplementι X T)).app U p,
      openInverseImageToOpenComplement_mem f T U p⟩
  naturality := by
    intro U V φ
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact congrArg (fun k ↦ k p)
      ((openInverseImageι f (openComplementι X T)).naturality φ)

/-- Postcomposing `openInverseImageToOpenComplement` with the open-complement
inclusion recovers `openInverseImageι`. -/
theorem openInverseImageToOpenComplement_comp_ι {S : Scheme.{u}}
    {X' X : AlgebraicSpace S} (f : X' ⟶ X) (T : Closeds (Points X)) :
    openInverseImageToOpenComplement f T ≫
        openComplementι X' (T.preimage (Points.continuous_map f)) =
      openInverseImageι f (openComplementι X T) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace

