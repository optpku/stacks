module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.Group
import StacksCheckRecall

@[expose] public section

section
variable {k : Type*} [Field k]

/- Definition 59.61.4: The Brauer group of a field is the group of similarity
classes of finite central simple algebras, with multiplication induced by tensor
product. -/
@[stacks 03R5] #check (BrauerGroup.instCommGroupBr : CommGroup (BrauerGroup k))
@[stacks 03R5] #check @BrauerGroup.one_def
@[stacks 03R5] #check @BrauerGroup.mk_mul_mk
@[stacks 03R5] #check @BrauerGroup.mk_inv

end

end
