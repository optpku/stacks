module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Lemma_67_9_7
public import stacks_project.Chap67.Remark_67_20_9_Factorization

/-!
# Stein properties of relative normalization

For a universally closed quasi-separated morphism of algebraic spaces, the
canonical map to the relative normalization is universally closed,
quasi-compact, quasi-separated and surjective, the structure-sheaf map of that
first factor is an isomorphism, and the relative normalization is uniquely
identified over the target with the relative spectrum of the pushed-forward
structure sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The canonical map from the source into the relative normalization of a
universally closed quasi-separated morphism of algebraic spaces is universally
closed. -/
instance instUniversallyClosed_toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] :
    UniversallyClosed (toNormalization f) :=
  sorry

/-- The canonical map from the source into the relative normalization of a
universally closed quasi-separated morphism of algebraic spaces is
quasi-compact. -/
instance instQuasiCompact_toNormalization_of_universallyClosed
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] :
    QuasiCompact (toNormalization f) :=
  sorry

/-- The canonical map from the source into the relative normalization of a
universally closed quasi-separated morphism of algebraic spaces is
quasi-separated. -/
instance instQuasiSeparated_toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] :
    QuasiSeparated (toNormalization f) :=
  sorry

/-- The canonical map from the source into the relative normalization of a
universally closed quasi-separated morphism of algebraic spaces is surjective. -/
instance instSurjective_toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] :
    Surjective (toNormalization f) :=
  sorry

/-- The structure-sheaf map of the canonical map into the relative
normalization of a universally closed quasi-separated morphism of algebraic
spaces is an isomorphism. -/
instance instIsIso_commRingStructureSheafMap_toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] :
    IsIso (commRingStructureSheafMap (toNormalization f)) :=
  sorry

/-- The relative normalization of a universally closed quasi-separated morphism
of algebraic spaces is uniquely isomorphic over the target to the relative
spectrum of the pushed-forward structure sheaf. -/
theorem existsUnique_iso_toPushforwardRelativeSpec
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] :
    ∃! e : normalization f ≅ relativeSpec (pushforwardStructureQcAlgebra f),
      toNormalization f ≫ e.hom = toPushforwardRelativeSpec f ∧
        e.hom ≫ relativeSpecπ (pushforwardStructureQcAlgebra f) =
          fromNormalization f :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
