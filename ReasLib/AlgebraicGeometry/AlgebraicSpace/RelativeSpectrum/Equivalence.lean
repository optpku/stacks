module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Qcqs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Pullback

/-!
# Affine algebraic spaces and quasi-coherent algebras

Pushforward of structure sheaves defines a contravariant functor on algebraic
spaces affine over a fixed algebraic space. This functor is an anti-equivalence
compatible with arbitrary base change.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver

/-- A morphism over `X` induces the contravariant map of pushforward structure algebras. -/
def pushforwardMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Y Z : AffineMorphismOver X} (h : Y ⟶ Z) :
    pushforwardStructureQcAlgebra Z.obj.hom ⟶
      pushforwardStructureQcAlgebra Y.obj.hom :=
  ObjectProperty.homMk (Under.homMk
    ((commRingPushforward Z.obj.hom).map (commStructureSheafMap h.hom.left) ≫
      (commRingPushforwardComp h.hom.left Z.obj.hom).hom.app
        (commStructureSheaf Y.obj.left) ≫
      eqToHom (congrArg (fun f : Y.obj.left ⟶ X ↦
        (commRingPushforward f).obj (commStructureSheaf Y.obj.left)) h.hom.w))
    sorry)

/-- The map on pushforward structure algebras induced by an identity is an identity. -/
theorem pushforwardMap_id {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : AffineMorphismOver X) :
    pushforwardMap (𝟙 Y) = 𝟙 (pushforwardStructureQcAlgebra Y.obj.hom) :=
  sorry

/-- Pushforward structure algebra maps reverse composition of morphisms over the base. -/
theorem pushforwardMap_comp {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Y Z W : AffineMorphismOver X} (h : Y ⟶ Z) (k : Z ⟶ W) :
    pushforwardMap (h ≫ k) = pushforwardMap k ≫ pushforwardMap h :=
  sorry

/-- The contravariant functor sending an affine morphism to its pushforward structure algebra. -/
def pushforwardFunctor {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (AffineMorphismOver X)ᵒᵖ ⥤ X.QcAlgebraUnder where
  obj Y := pushforwardStructureQcAlgebra Y.unop.obj.hom
  map h := pushforwardMap h.unop
  map_id Y := pushforwardMap_id Y.unop
  map_comp h k := pushforwardMap_comp k.unop h.unop

/-- The object assignment of the pushforward functor is pushforward of the structure sheaf. -/
theorem pushforwardFunctor_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (Y : (AffineMorphismOver X)ᵒᵖ) :
    (pushforwardFunctor X).obj Y = pushforwardStructureQcAlgebra Y.unop.obj.hom :=
  rfl

/-- The morphism assignment of the pushforward functor is the contravariant structure map. -/
theorem pushforwardFunctor_map {S : Scheme.{u}} (X : AlgebraicSpace S)
    {Y Z : (AffineMorphismOver X)ᵒᵖ} (h : Y ⟶ Z) :
    (pushforwardFunctor X).map h = pushforwardMap h.unop :=
  rfl

/-- An anti-equivalence is a pushforward anti-equivalence when its functor is naturally
isomorphic to pushforward of structure algebras. -/
def IsPushforwardEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S)
    (e : (AffineMorphismOver X)ᵒᵖ ≌ X.QcAlgebraUnder) : Prop :=
  Nonempty (e.functor ≅ pushforwardFunctor X)

/-- The pushforward condition is exactly the existence of a natural isomorphism with
the structure-algebra pushforward functor. -/
theorem isPushforwardEquivalence_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    (e : (AffineMorphismOver X)ᵒᵖ ≌ X.QcAlgebraUnder) :
    IsPushforwardEquivalence X e ↔ Nonempty (e.functor ≅ pushforwardFunctor X) :=
  Iff.rfl

/-- Algebraic spaces affine over `X` are anti-equivalent to quasi-coherent `𝒪_X`-algebras
through pushforward of structure sheaves. -/
theorem exists_pushforwardEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ∃ e : (AffineMorphismOver X)ᵒᵖ ≌ X.QcAlgebraUnder,
      IsPushforwardEquivalence X e := sorry

/-- A pushforward anti-equivalence is compatible with base change when geometric base
change corresponds naturally to pullback of quasi-coherent algebras along every base morphism. -/
def IsBaseChangeCompatible {S : Scheme.{u}} (X : AlgebraicSpace S)
    (eX : (AffineMorphismOver X)ᵒᵖ ≌ X.QcAlgebraUnder) : Prop :=
  IsPushforwardEquivalence X eX ∧
    ∀ {X' : AlgebraicSpace S} (g : X' ⟶ X),
      ∃ eX' : (AffineMorphismOver X')ᵒᵖ ≌ X'.QcAlgebraUnder,
        IsPushforwardEquivalence X' eX' ∧
          Nonempty ((baseChange g).op ⋙ eX'.functor ≅
            eX.functor ⋙ QcAlgebraUnder.pullback g)

/-- Base-change compatibility is the pushforward condition together with natural
comparison isomorphisms to algebra pullback after every base change. -/
theorem isBaseChangeCompatible_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    (eX : (AffineMorphismOver X)ᵒᵖ ≌ X.QcAlgebraUnder) :
    IsBaseChangeCompatible X eX ↔
      IsPushforwardEquivalence X eX ∧
        ∀ {X' : AlgebraicSpace S} (g : X' ⟶ X),
          ∃ eX' : (AffineMorphismOver X')ᵒᵖ ≌ X'.QcAlgebraUnder,
            IsPushforwardEquivalence X' eX' ∧
              Nonempty ((baseChange g).op ⋙ eX'.functor ≅
                eX.functor ⋙ QcAlgebraUnder.pullback g) :=
  Iff.rfl

/-- Every algebraic space admits a pushforward anti-equivalence between algebraic spaces
affine over it and quasi-coherent algebras compatible with arbitrary base change. -/
theorem exists_baseChangeCompatiblePushforwardEquivalence {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∃ eX : (AffineMorphismOver X)ᵒᵖ ≌ X.QcAlgebraUnder,
      IsBaseChangeCompatible X eX := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver
