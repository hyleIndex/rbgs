# 写 running example 用的改动指南（第 2 版，2026-10-13；§9 按 G-3 第 2 轮审稿更新）

第 2 版吸收了三个独立审稿人逐条核对第 1 版后提出的 52 条勘误（对照 Coq、论文行号和决策记录），并加入了 G-3（ARMv8）审稿的结论。行号来自当日快照，Coq 名称为全限定名的末段。工具链为 Rocq 9.3.0，**未**在项目锁定的 9.2.0 上复核。

> **三条最重要的提醒**
> 1. 新 running example（缓冲单元版 SeqLock）的**设计已定，正确性定理尚未证明**。计划原先估算完整 Tier B 约需 20–28 个 Writer 迭代，目前已用约 5 个，尚无更新的估计。论文可以**描述**设计，暂时**不能引用**它的正确性定理，也没有新客户端性质可引（N-3 计划中）。
> 2. **新结果全部未提交（commit）。** 引用前你必须先 commit。在 9.3.0 下全量构建缺一个文件（`structures/DCPOs.v`，因为 `is` 成了保留字），artifact 说明要提到这一点，或者在 9.2.0 上复核。
> 3. **范围改成 oMCA，推翻了作者回应 A2 的承诺**："we rather restrict our scope to MCA, not oMCA"（popl2027-reviews.md:437）。新的 Scope 段必须明确说明这一改变，以及原因（Q6、Q6-2）。

---

## 1. 你已经做出的决定

| 主题 | 决定 |
|---|---|
| 范围 | **oMCA**：store forwarding 在范围内，POWER/ARMv7 不在。这与回应 A2 相反，见上面的提醒 3 |
| Running example | 带 `rmb`/`wmb` 的 SeqLock，加一个客户端单元 z；塔结构为 Counter → TicketLock → SeqLock |
| **命名（重要）** | "COH SeqLock / COH[z]" 是**重构前**的叫法。重构后单元是**缓冲单元**（Buf[x]、Buf[y]、Buf[z]，契约由 `I_tab` 给出），对象是 marker 契约下的 SeqLock ⊎ Buf[z]。论文**不要**再称它们为 "COH cells" 或 ν_COH[z]（那是 trace.tex:205 的寄存器）。"COH" 只用来指旧的寄存器单元开发 |
| 旧示例 | 印出的 TSO SeqLock（无屏障，rd ↦ rfence，wrt ↦ lfence）撤下或改标注 |
| 排序表 | 类别表 `WindowTable.dto` 进正文，四个 fence mode 作为它的矩形特例。注意：论文的**一般**接口和张量定义如果改用类别加表来写，在 Coq 的框架层（`models/`）**没有**对应物，只有示例层（`WindowTable`、`WindowLinkTable`）用到表。要么安排移植，要么说明一般定义只以 fence-mode 形式机械化 |
| Store forwarding（Q6） | 用缓冲单元重构，**只换对象规约**；类别、表、I、futures 程序、窗口都不变 |
| 导出接口 | marker 规约（§3.3） |
| 硬件范围 | 计划包括 x86-TSO 和 ARMv8。内存约定是"写在发出时返回"。**ARMv8 现有新问题待你决定（§9）** |
| 印出的程序 | 印实际验证的 futures 程序，并点名偏差（§2.2） |
| 深度 | Tier B 务实版：Counter 是原子 faa 寄存器上的近恒等模块；`memory/` 落地用历史层面的声明式桥（G-1）；x86 端到端定理可选 |
| 旧寄存器单元结果 | 从论文机械化表中撤下，留在仓库 |
| LatchSet | 直接建在缓冲单元上，等 Phase 1–2 完成 |

---

## 2. 代码

### 2.1 SeqLock 源码（`SeqLockCOH.v` 头注释），以及 §9 中的可能改动
```
write(vx,vy) = l.acq(); wmb; x.wrt(vx); y.wrt(vy); wmb; l.rel()
read()       = do { s <- l.get_ticket(); rmb; a <- x.rd(); b <- y.rd(); rmb }
               while (l.test_ticket(s))
```
TicketLock：
- `acq = t <- nxt.faa(2); while (own.get() <> t) {}; own.inc()`
- `rel = own.inc()`
- `get_ticket = own.get()`
- `test_ticket(s) = (s & 1) || own.get() <> s`：s 为奇数时不发出调用。

它取代 Appendix/SeqLock.tex:5–25 中的 TicketLock 代码。

### 2.2 实际验证的 futures 程序（`SeqLockProg.v`:219–251）与源码的偏差
- `acq` 之后、`get_ticket` 之后各多一个 wait；失败的那一轮在重试前要等 f1、fx、fy、f2。
- **依赖标签是位置式的**，即"已解析的全部句柄"。它比 impl.tex:139 按语法定义的标签更多，因此论文必须说明：running example 的标签**不是** impl.tex:139 的标签，或者给出理由说明位置式标签相对它是 sound 的。
- 只删掉两个 wait **不能**让程序等于 ⟦源码⟧。

---

## 3. 接口

### 3.1 类别和表
- 覆盖层（overlay）类别：write ↦ Wmb，read ↦ Rmb，zw ↦ DW，zr ↦ DR。TicketLock（plainTL）：acq、rel ↦ DRMW；get_ticket、test_ticket ↦ DR。
- `dto c d`（c 在前、d 在后，跨对象）为真，即该对**被排序**，当且仅当以下任一成立：
  - c 是 acquire 类，或 d 是 release 类；
  - W→wmb、wmb→W、wmb→wmb、R→rmb、rmb→R、rmb→rmb 之一；
  - （仅 rcsc）release 写后接 acquire 读。
- 覆盖层半独立关系 I_F（`findep`）：不同组件，且 dto **不**排序。
- **完整的 I_F**：SeqLock 内部的对全部有序。z 与 SeqLock 之间：
  - **有序**：zw→write、read→zr、write→zw、zr→read；
  - **无序**：zr→write、read→zw（因此允许 LB），以及 write→zr、zw→read（因此允许 SB）。

### 3.2 必须写进论文的反驳
- **印出的签名被反驳**：rd ↦ rfence、wrt ↦ lfence、I = ∅（`seqlock_lb_paper_tensor`，用论文自己的张量规则，对任意 I_SeqLock、I_z、z 的 mode 都成立）。反驳所用的执行是一个完整的模块执行，它的底层部分**相对论文自己的寄存器底层规约**是 rel_lin 的。这足以反驳印出的签名，但这个执行不是经过硬件验证的执行。另有见证层的 `paper_signature_fails`、`paper_modes_fail`。
  - 注意：这个反驳属于旧寄存器开发（`SeqLockLB`）。**是否作为"例外"保留在论文中，需要你批准**（§7）。
- **四个 fence mode 表达不了这个示例**：`four_modes_force_local` 和 `torn_with_local_tl`（见证层），这两条用了 `vm_compute`，要在机械化表中注明。`wmb_not_rectangular` 目前只对一个玩具表证明了。

### 3.3 新的导出规约：marker 规约（设计已定，**未证明**）
- SeqLock 是原子二元组寄存器 `nu_sl`，初值 (0,0)，按线性化点排序。
- 每个 write 带一个隐藏的**发布标记**：位于它第一个 wmb 的 flush 处，并且在**任何线程**的下一个 SeqLock 操作之前。
- 它与 Buf[z] 通过**从 findep 读出的契约**组合，形成**契约张量，不是 ⊗**。论文要说明这个示例不用 ⊗。
- **为什么不是 ⊗**：方法"完成"指的是**返回**，不是**发布**。用缓冲单元时，一个已返回的方法可能还有未发布的写。impl.tex:139 和回应 A21 的措辞要相应说明（§5）。
- 推论（计划中）：⊆ ν_{I_F}[{sl,z}] ∩ Lin_sl，也就是"两地址缓冲内存"。
- 允许 Q6、LB、SB；禁止经过 z 的 MP（两个方向）和 OOTA。

### 3.4 底层规约（新设计）
| 部分 | 状态 |
|---|---|
| x、y、z 是 `memory/` 的缓冲单元，契约由 `I_tab` 给出 | **已证明**（F-1：`TableBarrier`） |
| 屏障是两个不同的幽灵地址：wmb 写 `GBw`，rmb 读 `GBr`。rmb 与 wmb 不排序，原因是 **dto 本身就不排序 Rmb/Wmb**，而两个不同的地址不会额外强加顺序 | **已证明** |
| TicketLock、own、nxt 保持原子；"原子子句"：原子操作之前，与它 dto 依赖的本线程待发布写必须已发布 | **未证明**（F-2，冻结中，见 §9） |
| 到 rel_lin 和模块语义的连接 | **未证明**（G-1、D-2） |
| 写在发出时返回，所以 z 无新鲜度 | 约定 |

---

## 4. 现在能引用的结果（已内核检查并经审稿；ARMv8 除外）

### 4.1 为什么寄存器单元不够（重构的动机）
| 主张（准确表述） | Coq | 公理 |
|---|---|---|
| Reviewer A 的 SB+rfi：寄存器单元在 I_TSO 下拒绝它 | `RegisterSB.sbrfi_not_rel_lin_TSO` | 无 |
| 只要 I 保留**两个同址 W→R 对**和**两个跨址读–读（R→R）对**，寄存器单元就拒绝它 | `RegisterSB.sbrfi_not_rel_lin_any` | 无 |
| **Mem.tex:13 字面上是错的**：在 I_loc（所有跨址对都独立）下它可线性化 | `RegisterSB.sbrfi_rel_lin_loc` | 无 |
| 准确说法（寄存器单元）：任何保留本线程同址 W→R、又允许 SB+rfi 的 I，也会允许 MP（`W x 1; W y 1 ‖ R y=1; R x=0`）或其镜像。"TSO 禁止 MP"本身**没有**内核化 | `RegisterSB.sbrfi_needs_rr_reordering` | 无 |
| 该结果在缓冲 TSO 单元中合法，并且是 x86-TSO 机器（读写片段）的轨迹 | `SeqLockQ6Mem.sbrfi_nu`, `sbrfi_x86_trace` | 无 |
| **Q6**：经过对象的 store-forwarding 结果被旧接口拒绝；对照实验 `q6_zr1_rel_lin`、`sb_rel_lin`、`d1/d2_rel_lin` 表明两条同线程链缺一不可 | `SeqLockQ6.q6_not_rel_lin(_any)` | 无 |
| 它的底层历史不满足寄存器底层规约（旧模块定理没错，只是假设不成立） | `q6_underlay_no_WF`, `q6_underlay_not_rel_lin(_any)`, `q6_module_hypothesis_fails` | 无 |
| 该历史的**手工映射**单元像在 memory/ 中合法，并且是 x86-TSO 读写片段的机器轨迹。其中每个 XCHG 编码为连续的 R;W;F 三元组；这个编码等于一次 locked RMW，是**论证**而非证明 | `SeqLockQ6Mem.sq_nu`, `sq_locked`, `q6_cells_x86_trace`；`q6_cells_TSO_consistent` | 最后一条用 `classic` |
| **Q6-2**：如果写在发出时返回，SeqLock 的寄存器底层规约（nuEc, sindep）会拒绝一个**无 forwarding** 的运行，而该运行的手工映射单元像是 x86-TSO 机器轨迹。**只检查了 x**，y 按对称性成立。"对任何寄存器单元、任何 I"以及"对 ARMv8"的说法**没有**机械化 | `SeqLockQ6.rt_iteration_not_rel_lin(_any)`；`SeqLockQ6Mem.rt_cells_nu`, `rt_cells_x86_trace` | 无 |

### 4.2 新设计的基础（F-1）
| 主张（准确表述） | Coq | 公理 |
|---|---|---|
| 表诱导的缓冲内存加幽灵屏障；对它成立声明式刻画 | `TableBarrier.I_tab`, `declarative_tab` | `classic` |
| **wmb**：W→wmb 与 wmb→W' 对任意 pre 都在 ppo 中；(W, W') 对任意 witness 在 **Dc⁺** 中（**不**在 ppo 中，因为跨址数据写之间 dto 为 false）。**rmb**：对任意 pre ⊇ po∖I_tab，R→rmb、rmb→R' 以及复合的 R→R' 都在 ppo 中 | `ppo_wmb_WW`, `ppo_rmb_RR` | 无 |
| 对写类别对称的表：两个句柄分配只要在每一对依赖的同线程写上顺序相同，flush 契约就相同。ν 层面以及与程序序句柄之间的桥接仍未完成（D-2/G-1） | `contract_handle_invariant` | 无 |
| **非空性**：在尊重可容许发出顺序（pre ⊇ po∖I_tab）的前提下，ν_{I_tab} 中**没有**历史能呈现 MP+wmb/rmb；**去掉**这个条件，该结果其实在 ν 中（`mp_wmb_rmb_nu_unordered`）。SB+rfi 在遵守全部 po 的情况下被允许。两者都是在 4 类别的抽象表 `ato` 上证明的；`ato` 与 dto 在 DR/DW/Rmb/Wmb 上一致，这一点只做了求值，没有记录进开发 | `NonVacuity.mp_wmb_rmb_forbidden`, `sbrfi_tab_po` | 前者用 `classic` |
| **x86 单元层落地**：每条 x86-TSO 读写机器轨迹都是 `V_{I_tab}` 的擦除，对**任何**表都成立；幽灵屏障插入在满足 FIFO 放置条件（作为假设）的位置时，结论保持 | `TableBarrierTSO.x86_trace_V_tab_index`, `x86_wmb_V_tab`, `x86_rmb_V_tab` | 无 |

x86 落地的限制：单向包含；无 RMW；无程序（发出序不等于程序序）；与 rel_lin 无连接；依赖 FIFO，**不能**搬到 ARMv8。

### 4.3 ARMv8：**只是相对模型的 litmus 级证据**（不属于"可引用"结果）
- 模型 `memory/ARMBar.v` 是 Writer 对 aarch64.cat 的读法（3 种读法），**未验证，herd7 未运行**。审稿人认为子句忠实，但 F2（RMW 的读与写是否由 si 连接）确实存疑。
- 即使 G-3 审稿通过、herd7 也跑完，ARMv8 证据仍然只是 litmus 级：**没有**类似 `x86_trace_V_tab` 的 ARM 定理，也**没有**到 rel_lin 的连接。
- 结论（相对模型）：
  - RSW through the object **禁止**（所有读法）；
  - SeqLockZ+rfi（Q6 的 ARM 版）**允许**；
  - 原子子句：任何 RMW 变体加普通 LDR 都能满足它的排序部分；
  - 写者一侧的"版本字"风险对 SeqLock 很可能不构成问题（M-16）；
  - **读者一侧有一个新问题，见 §9**。

### 4.4 旧寄存器单元结果（从论文表中撤下）
`SeqLockModule`、`SeqLockClients`、`SeqLockLB`。它们只覆盖"写返回即对所有线程可见、且无 forwarding"的 underlay。
- **是否保留作为"例外"（反驳或动机）由你决定**，我只是建议。候选：
  - `seqlock_lb_paper_tensor`（反驳印出的签名；见 §3.2 的限定）；
  - `seqlock_lb_not_classical`（**对象层**）和 `lb_underlay_not_classical`（**底层寄存器**层）：LB 在 **I = ∅ 的 relaxed linearizability**（不是 Herlihy–Wing 经典线性化）下被拒绝，作用在同一个模块执行上。
  - 如果不保留，就等 N-1 的缓冲单元版 T_lb。

---

## 5. 论文里要改或删的地方

| 位置 | 现状 | 怎么改 | 依据 |
|---|---|---|---|
| overview.tex:278；**figures/SeqLock.tex 全图**（:10–25、:29–70、:87–110、:121–132） | "two TSO data cells"，无屏障 | 换成带屏障的代码（§2.1，可能加 §9 的 rmb），单元是缓冲的；说明图中是否画出 z | Q6、D6 |
| trace.tex:393–396 | SeqLock 签名 I=∅、rd↦rfence、wrt↦lfence | 改成类别签名（§3.1），并说明印出签名被反驳 | `seqlock_lb_paper_tensor` |
| overview.tex:299–341；trace.tex:21、:348–355、:398–408 | fence-mode 的介绍和张量定义 | 定义 dto 和类别（W、R、Wmb、Rmb、DRMW…），四模式作为矩形特例；这也回应了 A9 | `abstract_is_rect`, `wc_is_special_case` |
| trace.tex:262 `rem:ra-tso`；Mem.tex:5、:658 | "RA and TSO coincide" | 删除或改写，把修正后的说法移到 Mem.tex | `sbrfi_not_rel_lin_TSO` + `sbrfi_x86_trace` |
| trace.tex:225–247（以及 `\hyperref[ex:IRIW]` 的引用处） | 用 IRIW 论证"COH 不是 MCA" | 删除 | 回应 A18 |
| **Appendix/Mem.tex:13** | "No choice of semi-independence relation repairs this" | 改为"no I that keeps same-location **and read–read** order repairs this" | `sbrfi_rel_lin_loc`、`sbrfi_needs_rr_reordering` |
| Mem.tex:19、:23、:223、:256–257、:394 | 无屏障、无 RMW；只对 TSO/PSO/RC | 如采用表实例：推广到 I_tab，写成**单向包含**（x86 轨迹 ⊆ erase(V_{I_tab})），不是等价；RMW 仍然没有 | `TableBarrier(TSO)` |
| Mem.tex:504、:566–567、:695（Δ2 机制） | "ob 里没有跨 po_loc 的子句"等 | 这些只对 POPL'18 版 ARM 模型成立；注明模型版本，并改成"crosses rfi, or po_loc into a read" | G-3 审稿 m-41 |
| relaxedlin.tex:126–153；overview.tex:343–357 | Def. 5.8 compatibility 和水平组合 | 改为窗口继承加 `window_link_table`（一个模块、分组件、positional 前提、仅完整执行）。`bracketed_not_compatible` **只适用于**四模式下的抽象锁括号组件。running example 上 Def. 5.8 失败，目前只是**求值事实**（(Acq, z.wrt) ∈ I_E 但 (write, zw) ∉ I_F），`seqlock_z_not_compatible` 是计划中的引理 | — |
| overview.tex:341、343–357（`prop:locality`）| "两个单元水平组合"与乘积 ⊗ 的水平组合 | **F-3 之后**：新的 running example（SeqLock ⊎ z，契约张量）**不是**乘积规则的实例，走的是联合规约版本 `WindowLinkTableJ.window_link_table_J`。论文要说明：**顺序论证仍按组件进行**（窗口、表、组件内顺序），但**规约义务变成一个联合义务**（在所有组件按 lp 排序的操作列表上），不再按组件分开证明。乘积情形是它的特例（`window_link_table_of_J`），两者可以互相推出。overview.tex:341 那句不再描述这个例子（审稿 m-50，**待你定措辞**） | `window_link_table_J`、`window_link_table_of_J`（已内核检查，无公理；还没有非乘积实例，等 S-2/D-2） |
| overview.tex:254–256 | Def. 2.1 的引入句 | 按 `RelaxedTraceLin.rhb`、回应 A5 和 A8 改写；条款 (i) 也适用于同线程 | — |
| overview.tex:276 | "every successful read observes values from the same update epoch" | 加限定：epoch 按值识别，不排除值巧合，**无新鲜度保证**；而且目前只对旧接口证明 | `seqlock_client_same_epoch`（旧） |
| overview.tex:278 | "两种 Counter 实现，TicketLock 证明不变" | 删除，或改为"对导出类别参数化"（见证层） | — |
| overview.tex:280–296；relaxedlin.tex:56–82 | 组合定理、观察精化 | 塔是一个内联模块；一般的垂直组合和观察精化**未机械化** | — |
| Appendix/SeqLock.tex（:3–8、:29、:47–57、:125） | 基于 TSO 版的 VLHL/RLHL 大纲 | 改为窗口路线（窗口 = write 的第一个 wmb、read 最后一轮的第一个 rmb，加 TicketLock 不变式）；TicketLock 的引入改为原子 nxt/own | — |
| intro.tex:113；implex.tex:187 | "Rocq verifies the SeqLock example"；HW 队列；exchanger 的"TSO underlay" | 说清楚验证的是哪个 SeqLock、在什么层次；HW 队列未机械化；exchanger 改写为"over the register cell with I_TSO"，或给出理由 | B-2、Q5 |
| intro.tex:112 | COH/RA "equivalent" | 未机械化，删除或降级 | B2 |
| intro.tex:110；main.tex:164（摘要） | "dependency-forced OOTA behaviors remain rejected"；摘要中关于 SeqLock 和 RLHL 的措辞 | **没有** Coq 结果表明 relaxed linearizability 或 futures/依赖机制能拒绝依赖导致的 OOTA；要么标为纸面结论，要么等引理 | M-5 |
| **impl.tex:139**；回应 A21 | 依赖标签按语法定义；"return discharges dependencies" | (1) running example 用的是位置式标签（§2.2）；(2) "完成"指返回而不是发布（§3.3） | — |
| **intro.tex:119 的现有 Scope 段**（含 IRIW 句和"dependencies are taken syntactically"句） | 现有 MCA 范围的表述 | 改写：oMCA；写在发出时返回；用缓冲单元处理 forwarding；x86 单元层已落地；ARMv8 待定（§9）。**明确说明与回应 A2 不同**，并说明用什么取代了 A2 中的 forwarding 注解方案 | Q6、Q6-2 |
| trace.tex:398–408 | 句柄是不相交和 | 与 Coq 的共享 (thread, handle) 键对齐，或给出理由 | A12 |
| relatedwork.tex:11 | 已引用 lin-TSO | 按 A22 修改；如果要补其他 TSO 线性化文献，请自己核实 | — |
| 新增：机械化表 | — | 每行写：结论、Coq 名、层次、假设、公理、`vm_compute`、Rocq 版本（9.3.0；DCPOs 问题） | A3 |

---

## 6. 措辞约束
- **客户端**：新 running example **目前没有已证明的客户端性质**（N-3 计划中）。可以描述方法："client properties are derived from the relaxed-linearizability witness, for every trace of the most general client"，但这偏离了回应 B4 的承诺（上下文精化），需要你决定（M-10）。
- **完整执行**：所有 rel_lin 和模块层结果只覆盖完整执行；内存层的包含结论（V/ν、x86 轨迹）不受此限制。
- 不要写"verified on a COH memory"，要写"relative to the cell specification"。
- **垂直组合**：没有一般定理。目前塔只在见证层、基于寄存器单元（`SeqLockTower`）；基于缓冲单元的单内联模块塔定理是计划（T-3），尚未证明。
- **SeqLock 不用 RLHL/VLHL 证明**，走窗口路线。
- **ARMv8**：即使审稿和 herd7 都完成，证据也只是相对模型的 litmus 级；没有 ARM 的落地定理，也没有到 rel_lin 的连接。另见 §9 的新问题。
- **z 无新鲜度。**
- **先前工作**：lin-TSO 已在 relatedwork.tex:11 引用。第 1 版里我写的作者和会议信息没有记录来源，请不要采用；如要补引用请自己核实。

---

## 7. 待你决定或执行的事项
| 编号 | 事项 | 影响 |
|---|---|---|
| **§9** | **已决定（2026-10-13）：方案 C，只声称 x86-TSO**，ARMv8 写成局限（TicketLock 接口和"等一个标志再读另一个单元"的接口——包括 LatchSet——在 ARM 上客户端可见）。代码不变 | F-2 解冻，但排在 LatchSet 之后 |
| **herd7** | 运行 `memory/herd/{x86,aarch64}/*.litmus`（命令见 `memory/herd/README.md`），报告版本、.cat 路径和判定 | 所有 ARMv8 说法、F2 读法、x86 SeqLockZ+rfi 判定都取决于它 |
| 例外 | 是否在论文中保留 §4.4 的旧结果作为反驳或动机 | §3.2 |
| M-10 | 客户端的措辞 | §6 |
| M-1/Q3 | 是否接受只覆盖完整执行；与 B4 的 "every completed abstract read" 有关 | — |
| Q1 | 论文是否声称 RLHL/VLHL 已机械化（目前 RLHL 编码是存在式的，未连接 rel_lin/GSimRel） | §6 |
| D5 | Δ3（以及 Δ2 是否保留为注记）要**在**改写 Scope 段和 Def. 2.1(i) **之前**决定 | §5 |
| OOTA | 内存层（依赖假设 (W)）、接口层（需对 marker 规约重新表述）或带 FutureD 的客户端模块 | intro.tex:110 |
| LatchSet | "write snapshot"的定义 | — |
| Mem.tex | 是否采用表实例、幽灵屏障和句柄不变性 | §5 |
| WriteSnapshot | **已决定：暂不机械化。** intro.tex:106 说"We verify LatchSet ... and an interval-linearizable write-snapshot"：论文**不能**声称 WriteSnapshot 已在 Coq 中验证（Coq 的 rel_lin 只支持顺序/原子目标规约）；LatchSet → WriteSnapshot 的垂直组合也没有 Coq（Coq 里没有一般的垂直组合定理） | intro.tex:106、overview.tex:270–350 |
| flush 事件 | **已决定：Coq 暂不跟进。** trace.tex 在 M_E 里加了 {flush, ok}、去掉了句柄名分量；Coq 的轨迹模型不变（flush 藏在规约内部）。论文若保留这个改动，要说明与 Coq 的差别 | trace.tex |
| LatchSet | **已决定：** 用 checker 里的有序数组 LatchSet（两份拷贝 + latch seq + wmb/rmb，contains 对 seq 读有地址依赖），单写者作为客户端前提。计划草案见 `.rocq-review/latchset-plan.md`（正在做设计审查） | overview.tex:270–331 |
| m-50 | 水平组合那一节怎么写：running example 不再是乘积 ⊗ 的实例，而是"⊗ 加一个契约"（联合规约）。审稿人建议 S-2 时证明一个分解引理，把联合义务拆成各组件义务加一个跨组件契约义务，这样论文可以写成"⊗ 加契约" | §5（overview.tex:341、343–357） |
| 其他 | Q2（关于 RC11/ARMv8 能说什么）、Q5（弱 HW 队列留或删）、D6（exchanger/EB stack）、D7 | — |

---

## 8. 进度
- **已完成**：SL-client、SL-nonvac（寄存器版，已撤出论文）；Phase 0（Q6 证据）；F-1（表内存、屏障、x86 落地）。
- **已完成**：G-3（第 2 轮审稿通过，循环关闭；结果是相对模型的，herd7 未跑）。
- **已完成**：F-3（联合规约版本的组合定理；审稿通过，循环关闭）。
- **已完成**：D-1（SeqLock 模块证明的执行桥接推广到任意底层规约；审稿通过，循环关闭）。结论：旧证明里**只有"有效性"（见证顺序能否按寄存器语义顺序重放）用到了寄存器规约**，其余（包括各组件内的顺序）对任何底层规约都成立。D-2 的入口已就绪：模块定理归结为两个义务，`nuJ []` 和联合规约义务 `p_S1J`（审稿人在内核里验证了这个组合）。
- **已完成**：T-1（内联模块 M0 及形状引理；审稿通过，循环关闭）。
- **你的决定（2026-10-13）**：LatchSet 优先；ARM 用方案 C；flush 事件暂不进 Coq；WriteSnapshot 暂不机械化。SeqLock 的 T-2/T-3（塔）降低优先级。
- **进行中**：LatchSet 计划的设计审查（主要风险：缓冲单元下单写者读到自己未发布的写，即 store forwarding）。
- **之后**：LatchSet 各阶段（LS-0..LS-7）；SeqLock 的 F-2 → S-1 → S-2 → D-2 排在后面。
- **注意**：没有任何新结果已 commit。

---

## 9. 屏障映射和 ARMv8 上的新问题（G-3 审稿，同日）

### 9.1 映射
| 抽象操作 | x86-TSO | ARMv8 |
|---|---|---|
| `wmb` | 不发指令 | `DMB ISHST` |
| `rmb` | 不发指令 | `DMB ISHLD` |
| `nxt.faa(2)`、`own.inc()` | `LOCK XADD` / `XCHG` | `LDADD`（任何变体都满足原子子句的排序部分） |
| `own.get()` | `MOV` | `LDR` |
| x、y、z 的读写 | `MOV` | `LDR` / `STR` |

### 9.2 问题（M-15）——**第 2 版更正：不是客户端可见的错误**
客户端写 `while (z.rd() != 1) {}; (a,b) = read();`，在 ARM 上会发生以下情况：
- **会发生**：read() 的第一个读（get_ticket）可以在 z 的读之前完成，读到 acq 之前的旧版本号。原因是 get_ticket 前没有屏障，而控制依赖不排序两个读（除非加 ISB）。这对 LDR、LDAR 和"控制依赖无 ISB"三种写法都成立。
- **不会发生**：read() 返回 (0,0)。get_ticket 之后那条 DMB LD 也把更早的 z 读排在了 x 读之前，test_ticket 会发现版本变了，于是读者**重试**。
- 内核证据（相对 G-3 的 ARM 模型，所有读法都成立）：
  - `MPObj.mp_obj_forbidden`：看到 z=1 之后 read()=(0,0) 是**禁止**的（`classic`）；
  - `MPObj.mp_obj_stale_get_allowed`：get_ticket 读到旧值是**允许**的（无公理）；
  - `RTGet.rt_get_allowed / _ldar_ / _ctrl_allowed`：同上；
  - `MPObj.mp_obj_prologue_stale_get_forbidden`：read() 开头加 DMB LD 后，读到旧值被**禁止**（`classic`）。
- **问题到底是什么**：SeqLock 在 ARM 上（至少在 MP-obj 这个形状上）**是正确的**。但我们的**证明**要求底层轨迹满足 Hν，而客户端的等待会引入一条实时边 zr → get_ticket；读到旧版本号的运行违反这条边，所以模块定理**不适用**于这类正确的 ARM 运行。性质与 Q6-2 相同：这是证明路线的缺口，不是客户端能看到的错误。"Hν 拒绝这条轨迹"目前是推导，F-2 会在内核里检查。
- **SeqLock ⊎ z 的其他客户端形状**（审稿人的逐项推导，未进内核）：等待之后接 read()、接 zr()、接 write() 或 zw()，都看不到错误。因此对这个接口，M-15 只是证明缺口。
- **审稿人第 2 轮补充：两处会变成客户端可见的错误**：
  - **(a) TicketLock 接口本身**。TicketLock 的原子实时规约在 ARM 上被 `rt_get_*` 违反，SeqLock 只是靠重试把它掩盖了。所以论文和 F-2 **不能**说 TicketLock 的模块定理对任意客户端在 ARM 上成立。
  - **(b) 任何"等一个标志、再读另一个普通单元"的接口**：`while (flag != 1); r = w`，即 Mem.tex 的 Δ3（MP+ctrl）。混合模型禁止这个结果，ARM 允许（`Sanity.mp_dmbst_ctrl_allowed`）。**LatchSet 和 Lock(O) ⊗ cell 都在这一类里**。
- **改规约修不好**：与 Q6-2 不同，换任何对象规约都无济于事，`own` 改成缓冲单元也一样，因为 acq 的写在 z=1 之前就已发布，get=0 仍然没有证人。只能改编译（B/A）、改范围（C）或改证明（D）。
- x86 不受影响。写者一侧的 R1/R2/R3 已被取代（M-16：对 SeqLock 很可能不构成问题）。

### 9.3 选择（第 2 版更正：问题是"证明能否覆盖 ARM"，而不是"代码在 ARM 上是否正确"）
| 选项 | 代码 | 能声称 | 代价 |
|---|---|---|---|
| **C：只声称 x86**（**审稿人建议论文现在用这个**） | 不变 | x86-TSO；ARMv8 写成局限：SeqLock 在 litmus 级看起来正确，但证明不覆盖；TicketLock 接口和多单元接口在 ARM 上需要额外屏障 | 最小；两边都有推导支撑，符合计划自己的范围规则 |
| **A：read() 开头加 rmb**（= B 只用在 SeqLock 上的特例） | `read() = rmb; do { s <- get_ticket(); rmb; a <- x.rd(); b <- y.rd(); rmb } while (test_ticket(s))`（ARM 上多一条 `DMB ISHLD`；x86 上无代价） | x86 和 ARMv8（待 herd7）。读到旧值被禁止（`mp_obj_prologue_stale_get_forbidden`，已有内核证据） | 印出的代码偏离 Linux 的 SeqLock，多出的 rmb **纯粹是为了证明**，论文要说明；**不覆盖 (b)**，LatchSet 仍要另想办法。审稿人：只在 B 被认为太宽时才用 |
| **B：编译规则**（**审稿人：ARM 的原则性路线**） | SeqLock 不变。规则：被等待的读编译成 `LDAR`，或"读 + `DMB ISHLD`"；结果被等待并影响后续写的 RMW 编译成"RMW + `DMB ISHST`"。对所有客户端适用 | x86 和 ARMv8（待 herd7）。统一解决 Δ3，**LatchSet 也需要它**；直接回答 Reviewer A 的 L786 | 改变代码映射（论文要写一句编译方案）；还缺一个引理 `rt_get_zr_ldar_forbidden`（m-45：`LDAR` 要放在**被等待的 z 读**上，不是 get_ticket 上） |
| **D：在较弱的底层假设下证明模块定理** | 不变 | x86 和 ARMv8；保留 rel_lin 和原版 SeqLock | 审稿人的读法：Hν 去掉"等待引起的读→读实时边"，需要一个新的 window-link 变体。工作量 XL，**建议推迟** |

`LDAR` 放在 get_ticket 上**没用**：它只排序之后的访问。B 要求把 `LDAR` 放在被等待的读（这里是 z）上，这样形成的环 acq W →(DMB ST) W z →rfe LDAR z →[A];po get=0 →fre acq W 在所有读法下都被禁止（审稿人推导，选 B 后补内核引理）。

**审稿人总结**：现在用 C；要声称 ARM 时走 B（A 是它在 SeqLock 上的特例）；D 推迟。这不是缓冲单元设计的缺陷，而是编译方案或范围的选择。
