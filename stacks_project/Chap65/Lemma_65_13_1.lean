module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Diagonal
import StacksCheckRecall

/-!
# Properties of the diagonal of an algebraic space

The diagonal of an algebraic space is automatically locally of finite type, a
monomorphism, separated, and locally quasi-finite in the sense of Definition 65.5.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 65.13.1 (1): let `S` be a scheme contained in `Sch_fppf` and let `F` be an
algebraic space over `S`. The diagonal morphism
`diag F : F.functorOfPoints ⟶ F.functorOfPoints ⨯ F.functorOfPoints` is locally of
finite type in the sense of Definition 65.5.1. -/
@[stacks 02X4]
#check (AlgebraicGeometry.AlgebraicSpace.locallyOfFiniteType_diag :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S),
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf (diag F))

/- Lemma 65.13.1 (2): let `S` be a scheme contained in `Sch_fppf` and let `F` be an
algebraic space over `S`. The diagonal morphism `diag F` is a monomorphism in the
sense of Definition 65.5.1. -/
@[stacks 02X4]
#check (AlgebraicGeometry.AlgebraicSpace.monomorphisms_diag :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S),
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf (diag F))

/- Lemma 65.13.1 (3): let `S` be a scheme contained in `Sch_fppf` and let `F` be an
algebraic space over `S`. The diagonal morphism `diag F` is separated in the sense of
Definition 65.5.1. -/
@[stacks 02X4]
#check (AlgebraicGeometry.AlgebraicSpace.isSeparated_diag :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S),
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf (diag F))

/- Lemma 65.13.1 (4): let `S` be a scheme contained in `Sch_fppf` and let `F` be an
algebraic space over `S`. The diagonal morphism `diag F` is locally quasi-finite in
the sense of Definition 65.5.1. -/
@[stacks 02X4]
#check (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_diag :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S),
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf (diag F))
