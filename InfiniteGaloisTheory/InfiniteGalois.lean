import InfiniteGaloisTheory.Basic

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace InfiniteGalois

lemma fixingSubgroup_IsClosed (L : IntermediateField k K) [IsGalois k K] :
  IsClosed (L.fixingSubgroup : Set (K ≃ₐ[k] K)) := sorry
--prove by pick nhds in the compl

lemma fixedField_fixingSubgroup (L : IntermediateField k K) [IsGalois k K] :
  IntermediateField.fixedField L.fixingSubgroup = L := sorry
--stick finite together

lemma fixingSubgroup_fixedField (H : ClosedSubgroup (K ≃ₐ[k] K)) :
  (IntermediateField.fixedField H).fixingSubgroup = H.1 := sorry
--by_contra and find a nhds (subgroup smul) and use 22.2

def intermediateFieldEquivClosedSubgroup [IsGalois k K] :
  IntermediateField k K ≃o ClosedSubgroup (K ≃ₐ[k] K)ᵒᵈ := sorry

end InfiniteGalois
