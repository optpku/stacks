module

public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

section

variable {S P : Scheme.{u}} {π : P ⟶ S} {ℰ : S.Modules}

-- The projective-bundle representation includes a relative-Proj presentation of its structure
-- morphism, whose separatedness follows from dependency 01O2.

/- Lemma 27.21.4: the structure morphism `π : P ⟶ S` of a projective bundle over `S` is
separated.

The project-local owner `Scheme.ProjectiveBundle.Representation π ℰ` derives this from its
explicit relative-Proj presentation using dependency 01O2. -/
@[stacks 01OD] #check
  (AlgebraicGeometry.Scheme.ProjectiveBundle.Representation.isSeparated :
    ∀ {S P : Scheme.{u}} {π : P ⟶ S} {ℰ : S.Modules},
      AlgebraicGeometry.Scheme.ProjectiveBundle.Representation π ℰ →
        AlgebraicGeometry.IsSeparated π)

end
