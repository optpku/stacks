module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Subcanonical
public import ReasLib.CategoryTheory.Sites.LocallySurjective

/-!
# Representability of quotient sheaves

This module constructs the canonical comparison from a quotient sheaf of a scheme
pre-relation to a representable sheaf and gives a local-surjectivity criterion for that
comparison to be an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- Composing with an equalizing morphism identifies points related by a pre-relation. -/
theorem quotientDesc_respects {S : Scheme.{u}} {U M T : Over S}
    (P : PreRelation U) (q : U ⟶ M) (h_equalizes : P.t ≫ q = P.s ≫ q)
    {x y : T ⟶ U} (hxy : P.pointRel T x y) :
    x ≫ q = y ≫ q := sorry

/-- The map on quotient-valued points induced by an equalizing morphism `q : U ⟶ M`. -/
def quotientDescApp {S : Scheme.{u}} {U M T : Over S}
    (P : PreRelation U) (q : U ⟶ M) (h_equalizes : P.t ≫ q = P.s ≫ q) :
    Quot (P.pointRel T) → (T ⟶ M) :=
  Quot.lift (fun x : T ⟶ U ↦ x ≫ q)
    (fun _ _ hxy ↦ quotientDesc_respects P q h_equalizes hxy)

/-- The quotient-valued point map induced by `q` is natural under precomposition. -/
theorem quotientDesc_naturality {S : Scheme.{u}} {U M : Over S}
    (P : PreRelation U) (q : U ⟶ M) (h_equalizes : P.t ≫ q = P.s ≫ q)
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    P.quotientPresheaf.map f ≫
        TypeCat.ofHom (quotientDescApp P q h_equalizes) =
      TypeCat.ofHom (quotientDescApp P q h_equalizes) ≫ (yoneda.obj M).map f := sorry

/-- The canonical map from the quotient presheaf to the representable presheaf induced by an
equalizing morphism `q : U ⟶ M`. -/
def quotientPresheafDesc {S : Scheme.{u}} {U M : Over S} (P : PreRelation U)
    (q : U ⟶ M) (h_equalizes : P.t ≫ q = P.s ≫ q) :
    P.quotientPresheaf ⟶ yoneda.obj M where
  app _ := TypeCat.ofHom (quotientDescApp P q h_equalizes)
  naturality _ _ f := quotientDesc_naturality P q h_equalizes f

/-- The presheaf descent map sends the quotient class represented by `x` to `x ≫ q`. -/
theorem quotientPresheafDesc_mk {S : Scheme.{u}} {U M T : Over S}
    (P : PreRelation U) (q : U ⟶ M) (h_equalizes : P.t ≫ q = P.s ≫ q)
    (x : T ⟶ U) :
    (P.quotientPresheafDesc q h_equalizes).app (op T)
        (Quot.mk (P.pointRel T) x) = x ≫ q := sorry

/-- The map `(P.t, P.s) : P.left ⟶ U ×_M U` induced by an equalizing morphism. -/
noncomputable def kernelPairLift {S : Scheme.{u}} {U M : Over S}
    (P : PreRelation U) (q : U ⟶ M) (h_equalizes : P.t ≫ q = P.s ≫ q) :
    P.left ⟶ pullback q q :=
  pullback.lift P.t P.s h_equalizes

/-- The first projection of `kernelPairLift` is `P.t`. -/
theorem kernelPairLift_fst {S : Scheme.{u}} {U M : Over S}
    (P : PreRelation U) (q : U ⟶ M) (h_equalizes : P.t ≫ q = P.s ≫ q) :
    P.kernelPairLift q h_equalizes ≫ pullback.fst q q = P.t := sorry

/-- The second projection of `kernelPairLift` is `P.s`. -/
theorem kernelPairLift_snd {S : Scheme.{u}} {U M : Over S}
    (P : PreRelation U) (q : U ⟶ M) (h_equalizes : P.t ≫ q = P.s ≫ q) :
    P.kernelPairLift q h_equalizes ≫ pullback.snd q q = P.s := sorry

/-- The canonical comparison from the quotient sheaf to the representable sheaf induced by an
equalizing morphism `q : U ⟶ M`. -/
noncomputable def quotientSheafDesc {S : Scheme.{u}} {U M : Over S}
    (P : PreRelation U) (J : GrothendieckTopology (Over S)) [J.Subcanonical]
    (q : U ⟶ M) (h_equalizes : P.t ≫ q = P.s ≫ q) :
    P.quotientSheaf J ⟶ J.uliftYoneda.{u + 1}.obj M :=
  (sheafificationAdjunction J (Type (u + 1))).homEquiv
      (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})
      (J.uliftYoneda.{u + 1}.obj M) |>.symm
    (Functor.whiskerRight (P.quotientPresheafDesc q h_equalizes)
      uliftFunctor.{u + 1, u})

/-- The quotient comparison factors the represented map induced by `q`. -/
theorem quotientSheafDesc_quotientMap {S : Scheme.{u}} {U M : Over S}
    (P : PreRelation U) (J : GrothendieckTopology (Over S)) [J.Subcanonical]
    (q : U ⟶ M) (h_equalizes : P.t ≫ q = P.s ≫ q) :
    P.quotientMap J ≫ P.quotientSheafDesc J q h_equalizes =
      J.uliftYoneda.{u + 1}.map q := sorry

/-- If an equalizing morphism and its relation-to-kernel-pair map are locally surjective in a
standard topology, then the canonical comparison from the quotient sheaf to the represented
target is an isomorphism. -/
theorem quotientSheafDesc_isIso_of_locallySurjective {S : Scheme.{u}}
    (τ : StandardTopology) {U M : Over S} (P : PreRelation U) (q : U ⟶ M)
    (h_equalizes : P.t ≫ q = P.s ≫ q)
    (h_q : Sheaf.IsLocallySurjective
      ((τ.overTopology S).uliftYoneda.{u + 1}.map q))
    (h_kernel : Sheaf.IsLocallySurjective
      ((τ.overTopology S).uliftYoneda.{u + 1}.map
        (P.kernelPairLift q h_equalizes))) :
    IsIso (P.quotientSheafDesc (τ.overTopology S) q h_equalizes) := sorry

/-- Locally surjective comparison maps canonically make the quotient-sheaf comparison an
isomorphism. -/
instance quotientSheafDesc_isIso {S : Scheme.{u}} (τ : StandardTopology)
    {U M : Over S} (P : PreRelation U) (q : U ⟶ M)
    (h_equalizes : P.t ≫ q = P.s ≫ q)
    [h_q : Sheaf.IsLocallySurjective
      ((τ.overTopology S).uliftYoneda.{u + 1}.map q)]
    [h_kernel : Sheaf.IsLocallySurjective
      ((τ.overTopology S).uliftYoneda.{u + 1}.map
        (P.kernelPairLift q h_equalizes))] :
    IsIso (P.quotientSheafDesc (τ.overTopology S) q h_equalizes) :=
  quotientSheafDesc_isIso_of_locallySurjective τ P q h_equalizes h_q h_kernel

end AlgebraicGeometry.Scheme.PreRelation
