module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport

/-!
# Scheme-theoretic support of a module on an algebraic space

A closed immersion is a scheme-theoretic support when it carries a
quasi-coherent pushforward model and is least among such closed immersions.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ofOverClosedSubscheme :
  ∀ {S : Scheme.{u}} (U : Over S)
    (I : U.left.IdealSheafData),
    AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.ofOverClosedSubschemeι :
  ∀ {S : Scheme.{u}} (U : Over S)
    (I : U.left.IdealSheafData),
    ofOverClosedSubscheme U I ⟶ ofOver U)

#check (AlgebraicGeometry.AlgebraicSpace.ofOverClosedSubscheme_spec :
  ∀ {S : Scheme.{u}} (U : Over S)
    (I : U.left.IdealSheafData),
    ofOverClosedSubscheme U I = ofOver (Over.mk (I.subschemeι ≫ U.hom)) ∧
      ofOverClosedSubschemeι U I = ofOverMap (Over.homMk I.subschemeι rfl))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.etalePullbackSchemeTheoreticSupport :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (F : X.Modules) (φ : ofOver U ⟶ X),
    U.left.IdealSheafData)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.etalePullbackSchemeTheoreticSupport_eq :
  ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (F : X.Modules) (φ : ofOver U ⟶ X),
    etalePullbackSchemeTheoreticSupport F φ =
      Scheme.Modules.schemeTheoreticSupport
        ((restrictToScheme U).obj ((pullback φ).obj F)))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsSchemeTheoreticSupport :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (F : X.Modules) (i : Z ⟶ X),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsSchemeTheoreticSupport.isClosedImmersion :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (F : X.Modules) {i : Z ⟶ X} [IsSchemeTheoreticSupport F i],
    IsClosedImmersion i)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isSchemeTheoreticSupport_iff :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (F : X.Modules) (i : Z ⟶ X),
    IsSchemeTheoreticSupport F i ↔
      IsClosedImmersion i ∧
        (∃ G : Z.Modules, G.IsQuasicoherent ∧ Nonempty ((pushforward i).obj G ≅ F)) ∧
          ∀ {Z' : AlgebraicSpace S} (i' : Z' ⟶ X) [IsClosedImmersion i'],
            (∃ G' : Z'.Modules,
              G'.IsQuasicoherent ∧ Nonempty ((pushforward i').obj G' ≅ F)) →
              ∃! k : Z ⟶ Z', k ≫ i' = i)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsSchemeTheoreticSupport.exists_lift :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} {F : X.Modules}
    {i : Z ⟶ X} [IsSchemeTheoreticSupport F i] {Z' : AlgebraicSpace S}
    (i' : Z' ⟶ X) [IsClosedImmersion i']
    (h : ∃ G' : Z'.Modules,
      G'.IsQuasicoherent ∧ Nonempty ((pushforward i').obj G' ≅ F)),
    ∃! k : Z ⟶ Z', k ≫ i' = i)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsSchemeTheoreticSupport.of_isLeast_closedSubspace :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (Z : ClosedSubspace X)
    (hQC : ∃ G : Z.X.Modules,
      G.IsQuasicoherent ∧ Nonempty ((pushforward Z.ι).obj G ≅ F))
    (hleast : ∀ Z' : ClosedSubspace X,
      (∃ G' : Z'.X.Modules,
        G'.IsQuasicoherent ∧ Nonempty ((pushforward Z'.ι).obj G' ≅ F)) →
        ∃ k : Z.X ⟶ Z'.X, k ≫ Z'.ι = Z.ι),
    IsSchemeTheoreticSupport F Z.ι)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.existsUnique_iso_of_pushforward_iso :
  ∀ {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} {F : X.Modules} (i : Z ⟶ X) [IsClosedImmersion i]
    (G G' : Z.Modules) [G.IsQuasicoherent] [G'.IsQuasicoherent]
    (e : (pushforward i).obj G ≅ F) (e' : (pushforward i).obj G' ≅ F),
    ∃! α : G ≅ G', ((pushforward i).mapIso α).trans e' = e)
