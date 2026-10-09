/-
  ABGV-5.2 —— **本体形式化 A · M2（EMTrans）**：格同构的载运（等变域同构）

  目标（蓝图 `wiki/proj-ABGV52-formalize-em.md` §3.1 M2／§2 #7／#18；
  路线 S 的 **S3**）：
    加法等变的格同构 `e : M ≃+ M'`（`e (g • m) = g • e m`）⟹ **等变函数域同构**
    `F(M) ≃ₐ[F] F(M')`，从而**不变量域同构** `F(M)^G ≃ₐ[F] F(M')^G`
    （`latticeInvariantsAlg` 形态，供 `IsRational` 消费）。

  三层载运：
    ① 单项式层：`mulEquivOfAddEquiv e : Multiplicative M ≃* Multiplicative M'`
       及与作用 `mulEquivOfSMul` 的**交换律**（等变性的代数量）；
    ② 格代数层：`latticeAlgebraTransport`（`MonoidAlgebra.domCongr`）＋
       与作用交换（`mapDomainRingEquiv_trans` 的范畴性）；
    ③ 函数域层：`latticeFieldTransport`（`IsFractionRing.algEquivOfAlgEquiv`）＋
       等变性（生成元上归约 ＋ `IsFractionRing.ringHom_ext`）；
    ④ 不变量域层：`latticeInvariantsAlgTransport`（`Subalgebra.val` ＋
       `AlgHom.codRestrict` ＋ `AlgEquiv.ofBijective`）。

  设计注记（TC 工程）：载运层（①–③）的**陈述不含 `G`**（`G` 仅出现在实例中）
  ⟹ 这些声明**不带 `G` 上下文**——否则在调用点 `?G` 悬空使 TC 卡死
  （"typeclass instance problem is stuck: SMulCommClass ?m ℤ M'"）。等变层
  （`_comm`／`_equivariant`／不变量域）才带 `G`。

  样板：`D13_ABGV52.lean:363–366`（`domCongr` ＋ `algEquivOfAlgEquiv`）、
  `D13_ABGV52.lean:434–464`（`codRestrict` ＋ `ofBijective`）。

  射程（A13）：本件只做**抽象格层**的载运。`Rep`-层的 `L ⊞ P ≅ Q` → 等变
  `AddEquiv` 的桥（#13）、Sym 呈现桥（#8）见后续件。

  **无 sorry、无自造公理**。
-/
import ABGV52.D3_ABGV52

namespace ABGV52
namespace EM

/-! ## 0. 不变量域的 `Field` 实例（一般形态；D13:364 只覆盖 `A → ℤ` 型） -/

/-- 不变量域（`Alg` 形态）的域结构：载体与 `latticeInvariants`（子域形态）相同。 -/
noncomputable instance (priority := 100) instFieldLatticeInvariantsAlg
    {F : Type*} [Field F] {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
    [Module ℤ M] [DistribMulAction G M] [SMulCommClass G ℤ M]
    [UniqueProds (Multiplicative M)] :
    Field ↥(latticeInvariantsAlg F G M) :=
  inferInstanceAs (Field ↥(latticeInvariants F G M))

/-! ## 1. 单项式层：`Multiplicative` 上的乘法等价与交换律 -/

/-- 加法同构的 `Multiplicative` 版本（显式构造，供 `_apply` 恒等式取 `rfl`）。 -/
noncomputable def mulEquivOfAddEquiv {M M' : Type*} [AddCommGroup M]
    [AddCommGroup M'] (e : M ≃+ M') : Multiplicative M ≃* Multiplicative M' where
  toFun x := Multiplicative.ofAdd (e x.toAdd)
  invFun x := Multiplicative.ofAdd (e.symm x.toAdd)
  left_inv x := by
    show Multiplicative.ofAdd (e.symm (e x.toAdd)) = x
    rw [AddEquiv.symm_apply_apply]
    rfl
  right_inv x := by
    show Multiplicative.ofAdd (e (e.symm x.toAdd)) = x
    rw [AddEquiv.apply_symm_apply]
    rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (e (x * y).toAdd)
      = Multiplicative.ofAdd (e x.toAdd + e y.toAdd)
    rw [show (x * y).toAdd = x.toAdd + y.toAdd from rfl, map_add]

@[simp] lemma mulEquivOfAddEquiv_apply {M M' : Type*} [AddCommGroup M]
    [AddCommGroup M'] (e : M ≃+ M') (x : Multiplicative M) :
    mulEquivOfAddEquiv e x = Multiplicative.ofAdd (e x.toAdd) := rfl

/-- **交换律**：`e` 等变 ⟹ 单项式等价与 `g`-作用交换。 -/
theorem mulEquivOfAddEquiv_comm {G : Type*} [Group G] {M : Type*}
    [AddCommGroup M] [Module ℤ M] [DistribMulAction G M] [SMulCommClass G ℤ M]
    [UniqueProds (Multiplicative M)] {M' : Type*} [AddCommGroup M']
    [Module ℤ M'] [DistribMulAction G M'] [SMulCommClass G ℤ M']
    [UniqueProds (Multiplicative M')] (e : M ≃+ M')
    (he : ∀ (g : G) (m : M), e (g • m) = g • e m) (g : G) :
    (mulEquivOfSMul G M g).trans (mulEquivOfAddEquiv e)
      = (mulEquivOfAddEquiv e).trans (mulEquivOfSMul G M' g) := by
  ext x
  show Multiplicative.ofAdd (e (g • x.toAdd))
      = Multiplicative.ofAdd (g • e x.toAdd)
  rw [he]

/-! ## 2. 格代数层：`F[M] ≃ₐ[F] F[M']` 与作用的交换 -/

/-- **格代数的载运**：单项式环之间的 `F`-代数同构。 -/
noncomputable def latticeAlgebraTransport {F : Type*} [Field F] {M : Type*}
    [AddCommGroup M] [Module ℤ M] [UniqueProds (Multiplicative M)] {M' : Type*}
    [AddCommGroup M'] [Module ℤ M'] [UniqueProds (Multiplicative M')]
    (e : M ≃+ M') : latticeAlgebra F M ≃ₐ[F] latticeAlgebra F M' :=
  MonoidAlgebra.domCongr F F (mulEquivOfAddEquiv e)

/-- **载运与作用交换**（格代数层）：`τ (g • a) = g • τ a`。 -/
theorem latticeAlgebraTransport_comm {F : Type*} [Field F] {G : Type*}
    [Group G] {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
    [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)] {M' : Type*}
    [AddCommGroup M'] [Module ℤ M'] [DistribMulAction G M'] [SMulCommClass G ℤ M']
    [UniqueProds (Multiplicative M')] (e : M ≃+ M')
    (he : ∀ (g : G) (m : M), e (g • m) = g • e m) (g : G)
    (a : latticeAlgebra F M) :
    latticeAlgebraTransport e (latticeAlgebraEquiv F G M g a)
      = latticeAlgebraEquiv F G M' g (latticeAlgebraTransport e a) := by
  show ((MonoidAlgebra.mapDomainRingEquiv F (mulEquivOfSMul G M g)).trans
        (MonoidAlgebra.mapDomainRingEquiv F (mulEquivOfAddEquiv e))) a
      = ((MonoidAlgebra.mapDomainRingEquiv F (mulEquivOfAddEquiv e)).trans
        (MonoidAlgebra.mapDomainRingEquiv F (mulEquivOfSMul G M' g))) a
  rw [← MonoidAlgebra.mapDomainRingEquiv_trans,
    ← MonoidAlgebra.mapDomainRingEquiv_trans,
    mulEquivOfAddEquiv_comm e he g]

/-! ## 3. 函数域层：`F(M) ≃ₐ[F] F(M')` 与等变性 -/

/-- **函数域的载运**（`IsFractionRing.algEquivOfAlgEquiv`）。 -/
noncomputable def latticeFieldTransport {F : Type*} [Field F] {M : Type*}
    [AddCommGroup M] [Module ℤ M] [UniqueProds (Multiplicative M)] {M' : Type*}
    [AddCommGroup M'] [Module ℤ M'] [UniqueProds (Multiplicative M')]
    (e : M ≃+ M') :
    latticeFunctionField F M ≃ₐ[F] latticeFunctionField F M' :=
  IsFractionRing.algEquivOfAlgEquiv (latticeAlgebraTransport e)

/-- 载运在生成元上的显式公式。 -/
theorem latticeFieldTransport_algebraMap {F : Type*} [Field F] {M : Type*}
    [AddCommGroup M] [Module ℤ M] [UniqueProds (Multiplicative M)] {M' : Type*}
    [AddCommGroup M'] [Module ℤ M'] [UniqueProds (Multiplicative M')]
    (e : M ≃+ M') (a : latticeAlgebra F M) :
    latticeFieldTransport e
        (algebraMap (latticeAlgebra F M) (latticeFunctionField F M) a)
      = algebraMap (latticeAlgebra F M') (latticeFunctionField F M')
          (latticeAlgebraTransport e a) := by
  show IsFractionRing.algEquivOfAlgEquiv (latticeAlgebraTransport e)
      (algebraMap (latticeAlgebra F M) (latticeFunctionField F M) a) = _
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]

/-- 作用在生成元上的公式：`g • algebraMap a = algebraMap (g • a)`。 -/
theorem latticeAction_algebraMap {F : Type*} [Field F] {G : Type*} [Group G]
    {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
    [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)] (g : G)
    (a : latticeAlgebra F M) :
    g • algebraMap (latticeAlgebra F M) (latticeFunctionField F M) a
      = algebraMap (latticeAlgebra F M) (latticeFunctionField F M)
          (latticeAlgebraEquiv F G M g a) := by
  show IsFractionRing.ringEquivOfRingEquiv (latticeAlgebraEquiv F G M g)
      (algebraMap (latticeAlgebra F M) (latticeFunctionField F M) a) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]

/-- **载运等变（函数域层）**：`τ (g • x) = g • τ x`。
证明：两侧都是 `K →+* K'` 的环同态，`IsFractionRing.ringHom_ext` 归约到
生成元 `algebraMap a`（三者：作用公式、载运公式、格代数层交换律）。 -/
theorem latticeFieldTransport_equivariant {F : Type*} [Field F] {G : Type*}
    [Group G] {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
    [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)] {M' : Type*}
    [AddCommGroup M'] [Module ℤ M'] [DistribMulAction G M'] [SMulCommClass G ℤ M']
    [UniqueProds (Multiplicative M')] (e : M ≃+ M')
    (he : ∀ (g : G) (m : M), e (g • m) = g • e m) (g : G)
    (x : latticeFunctionField F M) :
    latticeFieldTransport e (g • x) = g • latticeFieldTransport e x := by
  let f1 : latticeFunctionField F M →+* latticeFunctionField F M' :=
    (latticeFieldTransport e).toRingEquiv.toRingHom.comp
      (IsFractionRing.ringEquivOfRingEquiv
        (latticeAlgebraEquiv F G M g)).toRingHom
  let f2 : latticeFunctionField F M →+* latticeFunctionField F M' :=
    (IsFractionRing.ringEquivOfRingEquiv
      (latticeAlgebraEquiv F G M' g)).toRingHom.comp
      (latticeFieldTransport e).toRingEquiv.toRingHom
  have hhom : f1 = f2 := by
    apply IsFractionRing.ringHom_ext (A := latticeAlgebra F M)
    intro a
    change latticeFieldTransport e
        (IsFractionRing.ringEquivOfRingEquiv (latticeAlgebraEquiv F G M g)
          (algebraMap (latticeAlgebra F M) (latticeFunctionField F M) a))
      = IsFractionRing.ringEquivOfRingEquiv (latticeAlgebraEquiv F G M' g)
          (latticeFieldTransport e
            (algebraMap (latticeAlgebra F M) (latticeFunctionField F M) a))
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    rw [latticeFieldTransport_algebraMap]
    rw [latticeFieldTransport_algebraMap]
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    rw [latticeAlgebraTransport_comm e he g a]
  exact RingHom.congr_fun hhom x

/-! ## 4. 不变量域的载运 -/

set_option maxHeartbeats 800000 in
/-- 等变载运按不变量域成员关系可逆（`Alg` 形态）。 -/
theorem transport_mem_latticeInvariantsAlg {F : Type*} [Field F] {G : Type*}
    [Group G] {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
    [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)] {M' : Type*}
    [AddCommGroup M'] [Module ℤ M'] [DistribMulAction G M'] [SMulCommClass G ℤ M']
    [UniqueProds (Multiplicative M')] (e : M ≃+ M')
    (he : ∀ (g : G) (m : M), e (g • m) = g • e m)
    (x : latticeFunctionField F M) :
    latticeFieldTransport e x ∈ latticeInvariantsAlg F G M'
      ↔ x ∈ latticeInvariantsAlg F G M := by
  rw [mem_latticeInvariantsAlg_iff, mem_latticeInvariantsAlg_iff]
  constructor
  · intro h g
    apply (latticeFieldTransport e).injective
    exact (latticeFieldTransport_equivariant (F := F) (M := M) (M' := M') e he g x).trans (h g)
  · intro h g
    rw [← latticeFieldTransport_equivariant (F := F) (M := M) (M' := M') e he g x]
    exact congrArg (latticeFieldTransport (F := F) (M := M) (M' := M') e) (h g)

set_option maxHeartbeats 800000 in
/-- **不变量域的载运**（`Alg` 形态）：`F(M)^G ≃ₐ[F] F(M')^G`。 -/
noncomputable def latticeInvariantsAlgTransport {F : Type*} [Field F] {G : Type*}
    [Group G] {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
    [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)] {M' : Type*}
    [AddCommGroup M'] [Module ℤ M'] [DistribMulAction G M'] [SMulCommClass G ℤ M']
    [UniqueProds (Multiplicative M')] (e : M ≃+ M')
    (he : ∀ (g : G) (m : M), e (g • m) = g • e m) :
    ↥(latticeInvariantsAlg F G M) ≃ₐ[F] ↥(latticeInvariantsAlg F G M') :=
  let τ : latticeFunctionField F M ≃ₐ[F] latticeFunctionField F M' :=
    latticeFieldTransport e
  AlgEquiv.ofBijective
    ((τ.toAlgHom.comp
        (latticeInvariantsAlg F G M).val).codRestrict
      (latticeInvariantsAlg F G M')
      (fun x => (transport_mem_latticeInvariantsAlg (F := F) (M := M) (M' := M') e he (x : latticeFunctionField F M)).mpr x.2))
    ⟨fun x y h => Subtype.ext
        (τ.injective (Subtype.ext_iff.mp h)),
      fun y => ⟨⟨τ.symm y,
          (transport_mem_latticeInvariantsAlg (F := F) (M := M) (M' := M') e he _).mp (by
            rw [AlgEquiv.apply_symm_apply]
            exact y.2)⟩,
        Subtype.ext (τ.apply_symm_apply y)⟩⟩

set_option maxHeartbeats 800000 in
/-- 等变载运按 `latticeInvariants`（子域形态）的成员关系可逆。 -/
theorem transport_mem_latticeInvariants {F : Type*} [Field F] {G : Type*}
    [Group G] {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
    [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)] {M' : Type*}
    [AddCommGroup M'] [Module ℤ M'] [DistribMulAction G M'] [SMulCommClass G ℤ M']
    [UniqueProds (Multiplicative M')] (e : M ≃+ M')
    (he : ∀ (g : G) (m : M), e (g • m) = g • e m)
    (x : latticeFunctionField F M) :
    latticeFieldTransport e x ∈ latticeInvariants F G M'
      ↔ x ∈ latticeInvariants F G M := by
  rw [mem_latticeInvariants_iff, mem_latticeInvariants_iff]
  constructor
  · intro h g
    apply (latticeFieldTransport e).injective
    exact (latticeFieldTransport_equivariant (F := F) (M := M) (M' := M') e he g x).trans (h g)
  · intro h g
    rw [← latticeFieldTransport_equivariant (F := F) (M := M) (M' := M') e he g x]
    exact congrArg (latticeFieldTransport (F := F) (M := M) (M' := M') e) (h g)

set_option maxHeartbeats 800000 in
/-- **有理性沿等变载运不变**（`Alg` 形态；S5 组装所用变换）。 -/
theorem isRational_latticeInvariantsAlg_iff {F : Type*} [Field F] {G : Type*}
    [Group G] {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
    [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)] {M' : Type*}
    [AddCommGroup M'] [Module ℤ M'] [DistribMulAction G M'] [SMulCommClass G ℤ M']
    [UniqueProds (Multiplicative M')] (e : M ≃+ M')
    (he : ∀ (g : G) (m : M), e (g • m) = g • e m) :
    IsRational F ↥(latticeInvariantsAlg F G M)
      ↔ IsRational F ↥(latticeInvariantsAlg F G M') := by
  constructor
  · rintro ⟨n, ⟨h⟩⟩
    exact ⟨n, ⟨(latticeInvariantsAlgTransport e he).symm.trans h⟩⟩
  · rintro ⟨n, ⟨h⟩⟩
    exact ⟨n, ⟨(latticeInvariantsAlgTransport e he).trans h⟩⟩

/-! ## 5. 公理闸门 -/

#print axioms mulEquivOfAddEquiv
#print axioms mulEquivOfAddEquiv_comm
#print axioms latticeAlgebraTransport
#print axioms latticeAlgebraTransport_comm
#print axioms latticeFieldTransport
#print axioms latticeFieldTransport_algebraMap
#print axioms latticeAction_algebraMap
#print axioms latticeFieldTransport_equivariant
#print axioms transport_mem_latticeInvariantsAlg
#print axioms latticeInvariantsAlgTransport
#print axioms transport_mem_latticeInvariants
#print axioms isRational_latticeInvariantsAlg_iff

end EM
end ABGV52
