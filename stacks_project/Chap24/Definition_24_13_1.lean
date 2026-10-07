module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module
import StacksCheckRecall

@[expose] public section

/-!
# Definition 24.13.1

Right differential graded modules over a sheaf of DG algebras, their homomorphisms, and the
named category `Mod(𝒜, d)` are owned by `DifferentialGradedModule`, `Hom`, and `moduleCategory`.
-/

open SheafOfModules.RingedSite

/- Definition 24.13.1 (1): a right differential graded module over a sheaf of DG algebras is a
cochain complex of `𝒪`-modules with `𝒪`-bilinear right multiplications that are associative,
unital, and Leibniz. -/
@[stacks 0FRI] #check @DifferentialGradedModule

/- Definition 24.13.1 (2): a homomorphism of differential graded `𝒜`-modules is a map of complexes
of `𝒪`-modules compatible with multiplication. -/
@[stacks 0FRI] #check @DifferentialGradedModule.Hom

/- Definition 24.13.1 (3): the category of right differential graded `𝒜`-modules is denoted
`Mod(𝒜, d)`. -/
@[stacks 0FRI] #check @DifferentialGradedModule.moduleCategory
#check @DifferentialGradedModule.instCategory
