module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicGeometry.AlgebraicSpace

universe u v

variable {I : Type v} {S : Scheme.{u}} {X : AlgebraicSpace S}

/- Definition 74.22.3: descent data for algebraic spaces over algebraic spaces with respect
to a family of morphisms of algebraic spaces over a scheme `S` with fixed target, together
with their compatible componentwise morphisms. -/
@[stacks 0ADI] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData :
    (Xᵢ : I → AlgebraicSpace S) → ((i : I) → Xᵢ i ⟶ X) →
      Type (max (u + 1) v))

variable (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.ofObj Xᵢ f :
  Over X → DescentData Xᵢ f)

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen Xᵢ f :
  (sq : ∀ i j, ChosenPullback (f i) (f j)) →
    (∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)) →
      Type (max (u + 1) v))

variable (sq : ∀ i j, ChosenPullback (f i) (f j))
variable (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.ofIso Xᵢ f sq sq₃ :
  ∀ (V : ∀ i, Over (Xᵢ i))
    (φ : ∀ i j,
      ((overPseudofunctor S).map (sq i j).p₁.op.toLoc).toFunctor.obj (V i) ≅
        ((overPseudofunctor S).map (sq i j).p₂.op.toLoc).toFunctor.obj (V j))
    (hφ : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃),
    DescentData.Chosen Xᵢ f sq sq₃)

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.iso Xᵢ f sq sq₃ :
  ∀ (D : DescentData.Chosen Xᵢ f sq sq₃) (i j : I),
    ((overPseudofunctor S).map (sq i j).p₁.op.toLoc).toFunctor.obj (D.obj i) ≅
      ((overPseudofunctor S).map (sq i j).p₂.op.toLoc).toFunctor.obj (D.obj j))

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.cocycle Xᵢ f sq sq₃ :
  ∀ (D : DescentData.Chosen Xᵢ f sq sq₃) (i j k : I),
    Pseudofunctor.DescentData'.pullHom'
        (fun a b ↦ (DescentData.Chosen.iso Xᵢ f sq sq₃ D a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
      Pseudofunctor.DescentData'.pullHom'
        (fun a b ↦ (DescentData.Chosen.iso Xᵢ f sq sq₃ D a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (fun a b ↦ (DescentData.Chosen.iso Xᵢ f sq sq₃ D a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.hom_comm Xᵢ f sq sq₃ :
  ∀ {D E : DescentData.Chosen Xᵢ f sq sq₃} (ψ : D ⟶ E) (i j : I),
    ((overPseudofunctor S).map (sq i j).p₁.op.toLoc).toFunctor.map (ψ.hom i) ≫
        (DescentData.Chosen.iso Xᵢ f sq sq₃ E i j).hom =
      (DescentData.Chosen.iso Xᵢ f sq sq₃ D i j).hom ≫
        ((overPseudofunctor S).map (sq i j).p₂.op.toLoc).toFunctor.map (ψ.hom j))

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.equivalence Xᵢ f sq sq₃ :
  DescentData.Chosen Xᵢ f sq sq₃ ≌ DescentData Xᵢ f)
