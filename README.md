# todo
- test
- more about the landscape or history of ITPs
- say a little about Dependent type theory, CIC, Curry-Howard, add references
- Seperate mathmatical description from Lean
- (new) test changing lean version on a project.
- Check out some papers about automath
- check out paper "Calculus of Inductive Constructions" (paulin-Mohring maybe) and "calculus of constructoins" (Coqand)
- See foundations of mathematics section of Avigad's book "Mathematical logic and computation"
- Where does lean log changes to tactic functionality

# Math todos
- Define star free languages (with complement)
- Work on easy direction : L is star free -> M(L) has no nontrivial groups
- Characterize apierodicity as m, m^2, ... having no loop longer than one

# From reading
- Below: From Buzzard
- (what is an ITP) ITPs know the rules of a logic and the axioms of a theory, and can be used to prove theorems in the theory. One can think of an ITP as a programmming language where the code corresponds to mathematical definitions, theorems, and proofs. The user is expected to type in the key idea of the proof themself. A modern ITP will typically have tactics, which are little computer programs capable fo filling in steps which are clear to a mathematician but which would be tedious to prove from the axioms directly. Example: ring. Tactics make the process of taeaching a more advanced proofs to the ITP feasible i na reasonable time. However, it is still far more time=consuming than writing the analogus results in LaTeX. Historically ITPs were used by computer scientists to verify basic results in undergraduate mathematics. This centure users became more ambitious (ex: 2004 avigad verified the prime number theorem in Isabelle, arguablly the first serious result). More recently, the Lean community have been demonstrating that it isnow possible to formalize modern research level mathematics "in real time".
- (Mathlib) Mathlib now contains essentially all of a standard undergraduate mathematics degree, as well as many results at a masters level in algebra, number theory, and algebraic geometry. The library grod daily, and more and more mathematicians are getting involved.
- Below: From Avigad:
- (logic background for formalization) One of the most striking contributions of modern logic is its demonstration that matematical definitions and proofs can be represented in formal axiomatic systems.
- (begining of proof assistants and ITPs) The development of the first computational proof assistants around 1970 inaugerated a new era in which it has become possible to carry out formalization in practice. We can now write mathematical definitions, theorems, and proofs in idealized languages, like programming lagnuages, that computers can interpret and check. Young mathematicians everywhere are ennthusiastically contributing to the development of digital repositories of mathematical knowledge that can be rpocessed, verified, shared, and searched by mechanical means.
- (formal verification) Proof assistants are used by computer scientists to verify that hardware and software meet their design specifications, a practice known as formal verification. The matematical analogue is verifying the correctness of a mathematical proof, a task which is most compelling when the correctness of the original theorem is in doubt. (for example, in proofs that have extensive use of computation)
- (ITPs for ensuring correctness) in 2022, Thomas Bloom and Bahavik Mehta solved a problem, showing that any set of natural numbers with positive density has a finite subset whose reciprocals sum exactly to one. Within a few months, they verified the correctness of the proof in Lean, while the paper was still under review. This is probably the first time that a serious contemporary result in mainstream mathematics desn't have to be checked by a referee, because it has been checked formally.
- (ITPS for ensuring correctness of literature) In addition to helping us verify correctness at the outset, formal verification also helps us discover and correct errors in the mathematical literature. Formalization can help us get the details right.
- (Formalization leads to new insights) Formalization generally requires us to revisit and revise our proofs. A common theme in the literature is formalization leading to new insights.
- (formal libraries) Before one can formalize cutting-edge results, one has to formalize all the parts of mathematics they depend on, from elementary arithmetic and algebra to undergraduage and graduate-level mathematics and beyond. Lean's library, Mathlib, is notable for its open-ended, collaboarative model. Formal repositories provide comprehensive sources of knowledge, helping to turn ithe cloud into ta moder-day library of Alexandria.
- (word processor for mathematics) (playing with assumptions) Once we have mathematics in a digital format, it can be searched, analyzed, and minipulated by the computer. We an modify a definition and then step thorugh our proofs interactily to make the corresponding changes. We can drop or modify a hypothesis to a theorem and see what breaks (personal example, removing finiteness). We can extract a particular inference in a long proof, turn it into a seperate lemma, and set about generalizing it. Proof assistants are like a word processor for mathematics, allowing us to tinker with and imporve or mathematics in much the same way that a word processor allows us to tinkeer with and imorve our writing. Formalizers often speak of "golfing" a proof, which is to say, re-engineering it so that it becomes shorter and more efficient. Formilization encourages us to refactor to break them into smaller, more mangage pieces, reduce dependencies between the parts, exract definitions and lemmas that highlight the key ideas, weaken hypothesis or strengthen conclutions. Theorems invaribly epend on prior results, and when a theorem in a formal library is strengthened or generalized, a proof assistant enables us to the the effects on downstream results right away and modify them accordingly. In contrast to traditional journals, digital repositiories for mathematical knowledge are designed to be revised and updated over time.
- (ITP providing understanding) Formalization encourages us to identify, name, and reuse abstractions that are implicit in the mathematical literature. The engineering that makes it easier to use the library also reviels mathematical understanding and connections.
- Mathematical understanding is fleeting, but formal verification brings a satisfying sense of closure. Digital technollgy offeres new ways to support mathematical discourse.
- (ITP for managing complexity) Formalization helps manage complexity: Modularig mathematical data by breaking it up into smaller pieces with clearly delineated interfaces enables us to deal with one piece at at time, focusing on the information that is relavant at any point in a proof and setting aside the information that isn't. Proof assistants help us switch context between different parts of a proof by telling us explicitly what information and assumptions are in play, and making sure we use definitions and theorems correctly. WIth the use of an ITP, contributors only need to keep track of the objects which are locally relevant, thereby reducing the conginitive load significantly. At the same time, these targets can be recursively borken into smaller components until they can be handled directly. This is particularly useful in collaborations as this allows for the work to be easily distribued among contributors ith potentially varying areas of expertise. an ITP keeps track of the complicated dependency graph of objects within a methematical project. This is done in the process of type-checking.
 - Comment on how this sometimes reduces mathmatical understanding and can hide semantics, making proof writinging feel like a syntactic game where you forget about the math and semantics behind it. 
- (FOrmal libraries) help manage a growing base of mathmatical literature. It provides a place to look if you want to see if a result is already solved by someone. It makes the connections between domains explicit.
- (feedback and gameifying) ITPs provide immeadiate feedback. When a proof is incorrect, or, at least, does ont provide enough detail for the computer to assess correctness, you know it right away. When the computer can confirm the correctness, they arlse know it right away, and it feels good. This is usefull pedagogically and can be become addicting and game-like. Making math more like programming makes it easier to learn for many people (think of how many people learned to code on their own).
- (Formal verification) is used by AWS, abble, and Facebook to verify the correctness of code. This is becoming more common in mathematics. ITPs are especially well suited to verification.
- (automated theorem proving) Automated reasoning can be employed, and in lean it can be used to solve many theorems in rings or that involve arithatic. Automated tools can currrently prove some simple things.
- (ITPs are being paried with LLMs) and more sybolic proof-search tools to attempt ot formalize automatically, to or learn mathematics. ITPs are a critically part of these systems to provide feedback and guidance. This requires desigining computational representations of mathematical objects in such a way that their porperties are avaliable to mechanical exploration.  Formalization will help pave the way to desigining such representations.
- Below: from Micheal Shulman
- (ITPS and logic background) At the core of a proof assistant is a program called the kernel that checks whether a proof is correct. The meaning of "correect" is determinded by a so-called foundational theory, which here simply menas a formal system that is expressive enough that "all of mathematics" can be encoded into it. The best known foundational theory is ZFC, expressed in first order logic. FOL supplies rules for construcing and proving things caleld "Propositions" (statements), whicle ZFC supplies axioms about things called "sets" that are used in such proofs. Anouther class of foundational theoreis is the dependentat type theores in the tradition of Martin-Lof. Rather than have seperate layers of propositions and sets, these theories have one layer with rules for construcitng and inhabiting things called types. Some types are treated like sets and used to build methmatical structures, while other sypes are tereated like proposiitons and used to prove things. Remarkably, the same rules for types specialize to the basic operations of both sets and posopositions. this is called the Curry-Howard correspondence. FOr instance, the cartesisan product set A x B and the conjoineed proposiiont "P and Q" are unified by the notion of a product type. Lean is built on Dependent type theory.
- In general, the kernel of a Proof assist takes as input a proof written in the language of the foundational theory,, and checks whether it correctly follows the rules. Such a formalized proof closely resembles a computer program, and a kernel is analogus to a compiler. However, because the kernel must be trusted implicitly, the foundational theory is generally as simple as possible. It is like a machine code for mathematics. The spart
- TODO: Explain how the curry howard correspondence also shows that mathmatical projets correspond to programming projects. As such, much of the tools and convienences of software engineering practaces (git for version management and collaboration) can be used on mathematical projects.
- (why we need ITPS for formalization) THe spartan nature of the foundational theory makes it tedious for a human to use directly, so proof assistants also incorperate an elaborator. This is like a compiler that translates "programs" (constructions and proofs) from a high-level langauge into "machine code" (the foundational theory) that can be "executed" (verified by the kernel). THe high-level language of a proof assistant is called its "vernacular", which implements features to allow vernacular proofs to look more like pencil-and-aper mathematics. Most designers of proof assitants conclude that type theories make better vernaculars than set theories do.
- Ther vernacular impoves on the foundational theory, burt today's vernaculars sill require more details thatn a mathematic ial would ordinalrioy write on paper. Thus, formalizing in a proof assistant is still a more substantial undertaking than writing it for human readers. However, in certain restriced domains, the vernaculars incorperate automation, which can gernerate a proof by appling algorihtms or searchin a library for applicable lemmas. Fore example ring in lean allows the lean proof to be acutaly simpler than the written version (albeat, while conveying less understanding)

- Below - From Andrew Granville
- (history of proof / what is a proof. Euclid, Hilbert, Godel) Mathematicians prove new statments by reducing them to those that have already been accepted as true. This recursive process must hae some starting point(s), some set of axioms - ideally elegantly formulated, as few as possible and consistent (we shouldn't be able to justify a statement and its negation from our axioms!) (soundness) - to start the proving. Moreover, it would be best if the axioms allow us to prove all the theorems we are interested in (completeness). As far as we know, Euclid made the first serious attempt to formulate axioms and these were refined and developed well into the twentieth century. However, Frege's widely touted system was inconsistant (Russell created paradoxes within the interpretation fo its language), and then Russsell and Whitehead's replacement was not entirly self-evident and was unwieldly to implement. These issues led Hilbert to suggest that we should be able to start from any set of consistent axioms and see where that leads; in other words, one does not have to start from immortal truths. It is the proofs that conjure the mathematics into existance. Hilbert's hope was to find a set of consistent axioms that are provably coplete. However, in 1931, Kurt Godel shook Hilbert's proposed mathematics to its foundations with his icompleteness theorems, which essentially say that no consistent system of axioms and rules that includes elementary arithmetic on the integers can be used to prove every true statement abou the integers, nor can it prove that system itself to be consistent. Disaster. Godels therems directly imply that "There can be no rigorous justification for classical mathematics" - John Von Neumann.
- (crisis response and ZFC) Most pure mathematicians deal with this irresolvable foundational crisis by ignoring it. For many mathematicians, Godel's objections seem to be irrelevant to what they are working on. They need a formal reasoning syste that is reliable in all reasonable circumstances. For the last century the basic axiomatic system (ZFC) has remained accepted as the essentially unchanged foundation for most of modern pure mathematics, despite Godel's results, and yet it works.
- (social standards of proof / proof vs understanding) We would like to believe that pure mathematics has objetive standards of proof, that any theroem has been rigerously justified back to the axioms. But who verifies this, and how? One would like a highly skilled objective verifier, a trusted authority who can verify that the language and deduction rules have been validly used all the way back to the axioms. In a formal proof every inference is laid out so that the proof can be mechanically verified, requiring no intuition. But would such a proof be convincing to mathematicians? "Proof supposedly establishes the undeniable truth of a piece of mathematics, but proof doesn't actually convince mathematicians of that truth ... Something else does." - Eugina Cheng. Proofs are accepted as correct by peers interested in similar questions and are aware of the techniques used in the field. The reader is not passive. Proof s accepted by these community standards might be wrong since the details are not carefully checked by the verifier (and indeed, most details are usually of less interest, as an experienced reader can reconstruct them) but the verifier is not looking for strict proof but rather understanding that allows the new work to be contextualized. proof and understanding are not synonymous, and we have to appreciate and accept how they match and how they differ. 
- (libraries) All proofs are constructed in a similar way: Staring from aggreed upon axioms we construct proof sof given statements. To advance far we need to avoid going back to the axioms all the time, so we need to build a library of statemnets that we know to be true and are unambiguously stated. Traditionally, this library is stored in research articles, and synthesized in books. Machines can also store this in their own language.
- (understanding) Formal proofs chase the details of a proof back to the axioms, like a child tirelessly asking "why?". But, at the end of that process, does the child remember what they asked at the start and how they got to the end? And when the formal proof-verifier reports that a proof si correct, then do we really undersand why any more than the child who is told, "because I told you so"?
- Computer assisted proofs assist in verifying the logic of an author's arguments, perhaps interactively. This has been most useful in cerifying long, detailed proofs, where angels fear to tread. For example, Gonthier and a team verified the 4 color theorem in Coq (a very long proof). As more researchers contrubute to the system (lean), interaction should move towards something resembling the high-level practice of mathematicians. With further work on the input and output languages, a system like this could be user-friendly and become an integral part of the mathematician's arsenal. The eventual proofs are not human-readable, but that could change with better venacular languages and translations to latex.
  
- From Micheal Harris -
- Historians of mathematics have been vigorously questioning the narratives around proof that are dominant in the wrigings of mathematicians; but these narratives, misleading as they often are, are at the basis of much of what is claimed regarding the implications of automation.
- - The tech industy's new attention to pure mathematics- as evidenced by the increasingly visable participation of Silicon Valley nginnerrs in conferences on automated mathematics, and the creation of the mulit[million dllar holkinson center for Formal Mathematics at CMU - appears to be unprecedented. But it's a safe bet that the industyr is no more interested in 'pure research' or 'mathematics for he sake of mathematics' than were in the French executives in 2009. Nor is the industy likely to be interested in protecting the free exchange of ideas that (for the most part) characterize our discipline. Silicon Valley is a kind of archipelago but it is also a place where dissent is ruthlessly suppressed.
  - One perspecive has dominated media coverage on both the question of proof verificatoin and that of automation of theorem proving, including the coverage in publications of mathematical societies. This perspective, which corresponds roughly to what I call the 'Central Dogma' provides the primary underpinning for the sence of urgency that drives much of the idscourse around the nature and role of proof in mathematics; it says roughly thtat a proof is valid if (and only if) it can be expressed in a formal symboic language. I call it a "dogma" because it endows projects of formal proof verification with an epistemological centrality that I dont think is justified. - It hardly requires specialized training to be aware that there was mathematics before formalism and thus that mathematics is likely to continue after this perspecife has outlived its usefulness. Formalism as an ideology represents only a blip in the long histoy of mathematics; its experation date, in other words ,is likely to arrive well before that of human mathermatics. - "that some proofs were to be read as a king of paradigm, the text of a proof was not read only as establishing a proposition, but also as a possible source for working techniques" from Chelma. Concieving mathematics on the model of a viedeo game, where the only goal is to win, misses this kind of reading, whtere the apprehension of the text by a necesssarily human reader is the reason for its existance. - The narrative that is taking shape radically misses the point of mathematics and subsitutes it a domesticated version drained of meaning. I find it enlightening to compare the prospect (of machines replacing human mathematicians) to a concert in which machines have replaced the audience rather than the performers. - The technological mindset banishes the contingent, repudicates the singluar, obsures the ineffable, discards whatever cannot be monitized. The understanding at which mathematicins aims is all of those things. - - (coment): This is an important quote. maybe quote this in the write up. - - Comment: connect this to the gameifying of mathmatics in proof assistants -
  -
  -   From silva De Toffoli "Proofs for a price: tomorrow's ultra-rigerous mathematical culture" - (ideal proofs vs mathematics in practice) a proof is a success term. This means that there is no such thing as a fallacious proof. If we find a substantial error in a putative proof, than we establish that our putative proof was no proof at all. It wasn't a real proof, and things that aren't real proofs, iven if they look like proofs, are no proofs. Saying that fallacious putative proofs aren't proofs at all cannot mean that putative proofs containing inor mistakes are no proofs because those are ubiquitous in mathematics; banning them would lead to excluding too many of the things that mathematicians are happy to call proofs. That is why essentially correct putative proofs are profs. A putative proof that is essentially correct may contain minor errs, but may neither contain errors that woud invalidate its conclution, or errors that would e too hard to fix. - Proofs don't whear their correctness on their sleeve. Checking the correctneess of a proof can be tough, and mathematics are not infallible in discerning genuine proofs from erroneous putative proofs. And this matters. A lot. Thiis seeminly obvous fact puts pressure on the idea that we can actually get what we care for, certainty. - (epistemology). One way to think aobut epistemic justiviation is to link it to theoretical rationality. I am justified in believing that the optimal way to pack spheres is the face-centered cubic packing, becuase tom Hales proved it. More mundanely, I am justified in believing that in my fruit basket there are four oragnes since I bought forur this morning and are none. Both beliefs are rational since they are based on good reasons. But I could go wrong, like in the following case. unbenown to me, my friend Agnese sneakily took an orage an hour ago, and now there are only three oragnes in my fruit basket. In this case, I have a false but justified belief. This impleis that justivation in general is not factive. That is, it does not entail truth. On the other hand KNOWLEDGE is factive. This is why justification alone is not enough fro knowledge. - According to the recieved view in the philosophy of mathematics, a good first-hand reasons for mathematical propositions that are not axioms are genuine proofs. Mathematical justification is only given by proofs. - dIFFERENTLY THAN IN OTHER DOMAINS, IN MATHEMATICS, FIRST-HAND JUSTIFICATOIN HAS OFTEN BEEN CONSIDERED BY PHILOSOPHERS TO BE FACTIVE. tHIS IS BECAUSE IT HAS BEEN ASSOCIATED With proofs. This is remarkable and would set mathematical justification apart from other types of justificatoin. As we saw, I could be wrong in believing emperical facts about oragnes. Yet in mathematics, if I am rational, it seems as if I cannot end up believing in something false. This is why, in mathematics, justification and knowledge have traditionaly been conflated. This is connected with the a priori nature of mathematics. There is no external experience that can mess up my justification. If the only good first-hand reasons to believe a mathematica lclaim are proofs, then only true beliefs can be justified. BUT THIS IS IN STARK CONTRAST WITH MATHATICAL PRACTICE ! From the perspectife of the working mathematician, it seems that wwe can also be justified in the absence of a proof. And this is not only in cases which we onpenl use semi-rigerous methods. This also holds when we think we are dealing with rigerous proofs. Case in point: Vladimir Voevodsky was awarded the Fields medal in 2002. In two different cases, he found errors in relults he had previously published. In one, he found a significant error in a result he though he had established, and it turns out it was outright false. It is plausable to think that beore he found the errors, Voevodsky was jusitifed in believing his results. But this implies that contrary to the recieved view, mathematical justificatoin, like other types of epistemic justificatoin, is not factive. That is, it is possible to hold a justified false belief in mathematics, one that is based on something that looks like a proof but is not. Mathematical justificatoin should therefore not be connected with proofs, but thwith what in previous work I called simil-proofs. These are arguments that look like proofs to the relevant subjects but may contains significant errors. Here is a working def: A SIMIL-PROOF is a mathematical argument that is taken to be a genuine proof by at leans one approporiately trained subject, but that might not be. Moreover, it satisfies the same standard of acceptability of the mathematical community to which it is addressed, and it has not been the object of serous critisism. In mathematical practice, it is common to call "froof" aso arguments that are not genuine proofs. - At a given time, simil-proofs are phenomonicacally indistingishable from proofs, but they might contain substantial mistakes. This means that not all simil-proofs are proofs. However, if a simil-proof contains a substantial mistake, this must be a subtle mistake that the mathematical community is blind to. The idea is that by performing a self-monitoring activity on itslef, the mathematical community gradually filters out all ernroneous simil-proofs so that only correct simil-proofs (which are proofs) remain. - Voevodsky's case suggests that beliefs based on fallacious simil-proof are justified. - Not al proofs are simil-proofs. An example is given by an argument that is a proof, but, for some reason, no mathematician recognizes it as a proof. This could be becuase of the fact that the argument looks fallacious even if it is not, or, if we endorse an abstract definition of proof, that it has not been considered by any mthematician at all. - part of the success of mathematics rests on the possiility that the mathematical community performs a self-monitoring activity. It is because of this that if simil-proofs are to provide justification, they might contain errors, but they cannot be ideiosynctatic arguments that nobody except a single subject could, in principle, grasp. They have the potential to be understood by mulitple matheticians. That is, they must be SHARABLE. Note that a sharable argument might not be the kind of thing that a single mathematician can grasp; excluding large proofs like the ones involving automated computations or large collaborations would be too restrictive. - - My comment: do formalized proofs fit into the "proof but not simil-proof" category? they may be correct, but what if only the kernel can actually check each step? What if it was created using an automated process and no human every understands the proof? Is mathmatics about wriing proofs or writing simil-proofs? Is there even any use to a proof that is not a sharable simil-proof? Is there any use to a formal and verified proof that is not sharable, human readable, and does not provide mathematical understanding? - Too-long simil-proofs are more and more customary in mathematics. unitl now, we have mostly relied on each other to check the correctness of our simil-proofs, but in the furture, we might need to ask for help from elsewhere. Computer proof assistants are tools tat allow us to create formal counterparts of our informal simil-proof and formally verify them if they are indeed correct. This tools could therefore help us implement a more thorough heck on our simil-proofs. Obvious canadates for formal verification are computer=assisted simil-proofs. A famous case is the one of the 4-color theorem. A formally verified simil-proofs was produced in 2005 by Georges Gothier. - Buzzard and other members of the Lean community took on the challenge of formalizing a central theorem in condenced sets. They managed to formalize the buld of the simil-proof in just six moths. This shows that computer proof assistants can indeed tackle cutting-edge mathematics in a reasonable amount of time. This project was done because People were consernec that such a foundational lemma was only read by a couple of mathematicins due to is complexity and specificity, and they wanted to be sure that it was correct. - It is plausible to think that computer proof assistants can greatly amplify our confidence in the correctness of our simil-proofs. However, we still fall shour of getting a 100% guarentee. The first is the potential presence of bugs in the kernel or compiler of the proof assitant. The second type of problem is trickier. It has to do with the faithfulness of the translation of informal results into formal statments. How can be be sur that what we formalize is indeed what we started with in the first place? Till, verification, although a major benefit of ultra-rigerous mathematic, is not hte only one. Sharability is also enhanced through formalizatoins. This might might sound suprising sence sharability is often lowered by the use of computational tools. In particular, computer-assited simil-proofs tend to be rather opaque and thus hard to grasp, thus scoring low on sharability. -(sharability) Sharability is not only in place to check which simil-proof actually amount ot proofs. It is also crucial for providing mathmatical understanidng. - The importance of understanding in mathematic is unquestionalbe. Mathmaticsions discover that what they really want is usually not some collection of answers - what they want is understanding. Some go as far to suggest that undersanding is the ultimate goal of the mathematical activity. - Formalization allows for the prospect of produing mathematical documents that allow readers to dynamically choose the level of detail and access backgorund kwnolege on demant. Tools like Alectryon will enable us to make documents which will allow links to dyamic web pages deplaying matematical details in a huan-readable form, and which will allow one to keep digging right down to the axioms. One could imagine error-free undergraduate textbooks also written in this way, where statements which a student cannot unders=ant can be inspected in more datils until difficulties are resolved. All these considerations show that computer proof assistants like lean could help us come up with better, more sharble simil-proofs that can be accessed in a personalized way. - The very process of feeding asimil-proof to a computer requires thinking hard about the structure and the details of the original simil-proofs, thus helping us gain additoinal underanding. - Computer proof assitants could also help us better access already available results by making new searchable databases possible. Moreover, with the developent of AI, they will become better at suggesting proof stratagies, thus aiding us in finding noew simil-proofs. - (conclution, important) Philosphers have traditionally thought that first-had mathematical justification of a propositoin is provided by proofs exclusivly - but thi sis a mistake. Looking at the practice of mathematics, we soon ralize that therre are compelling cases which a subject can be justified in believing a fase mathematical proposition (as in Veovodsky's case) or a true mathmatical proposition in virtue of a fallacious argument. Beign associated with simil-proofs rather than proofs, mathematical justification is fallible. But our individual fallability can be partially oversome by working together and checking each other's results. Problems arise, however, when our simil-proofs are too long or too technical; our fellow mathematicians might be too busy or just unable to scrutinize them. Proof assistants might finaly give us certainity. Or at least, given that there is still the possibility of bugs or mismatches between informal and formal statments, to something closer to cirtainty compared to what we generally get relying exclusivly on our human abilityes. The more computer assitsants are going to be used, the easier it will become to formalize new mathermatics - they weill become more flexable, and the libraries wil grow. It might become, at some point, a price we are willing to pay. This is mor so because the dream is to use these tools not only as verificatoin devices but also as amplifiers of human understaning. After all, mathematical understanding is what we might really need.
  -
  -   - Colin McLarty "pincare on the value of reasoning machines" - Poincare wrote, "Hilbert sought, so to speak, to put the [geometry] axioms in a form which could be applied by someone who did not underand the meaning since he had never seen either points, or a line, or a plane. Accering to Hilbert, the reasoning must reduce to purely mechanical rules. It must be possible to do deometry by servile application of those rules to the axioms without knowing what they mean." - Hilbert said the proofs in is Foundations of Geormetry must be valid independently of the meaning of the geometric terms. His axioms abstract away from any concrete meaning of the nonlogical vocabulary. But, Hilbert initially paid no attention to the logic. He offerend no formal logic, no did he say logic should reduce to mechanical rules. Then, Hilbert kicked off a new project in his talk "On the foundations of logic and arithmetic". This was to develop logic together with analysis in a common frame, so that proofs can be viewed as finite mathematical objects; then show that such formal proofs cannot lead to a ontradictoin. This reuction of proofs to finite strings of symbols subject to formal rules was a prerequisite for todays computerized proof. Hilbert, then Godel, then Turing and many more would thake the mathematical of proof far beyond anything poincare imagined. But from 1902 on, Poincar urged a specific reason to persue mechanizable proofs and only in 1904 did Hilbert begin posiing the problem in those terms. - Pincare says, "Hilbert wanted to cut the number of fundemantal axioms of geometry to a minimum and list them completely. But in reaoning where our minds are active, where intutioin still plays a role, in live reasionibng so to speak, it is hard ot avoid introducing some axiom or postulate which goes unnoticed. Thus oly after reducing all geometric reasoning to a purely mechanical form could he be sure he had succeded in his plan an dcompleted his work." In Hilbers's foundations of Geometry, he game no new theorems. Rather, Hilbert fully displayed the intutitions behind each theorem. Poincare declared mechanized proof a threat to research creativity and learning, but he found mechanizable proof essential to fully explicit understaning. For poincare, only mechanizability can guarentee that we have fully stated assumptions suffiecient for the theorems. - The delight for Poincar is how Hilbert used this to produce new geometries. Hilert's Foundations of Geometry gives far more axioms than Euclid because the standared of mechinizalble proof reveals many gaps in Eculids proofs, where inutitivily obvioussteps did not follow from Euclids states axioms. Each gap in turn is compatable with all that Euclid had stated, but different from what Eucid unconsiously accepted. Thus hilbert arrives at the non-Desarguesian and other new geometries that Poincare praised. - The take home message: A formal Theory T admits arbitrarily many different informal interpretatoins giving T as many different meanings. A computer wiht T encoded on it, and able to derive formal conclutions from T, does not also know informal interpetations of T. The programmers know the motivating informal interpetations and thus the relevant meanings of theorems derived in T. Programmers and logicians can both say " The intellegence is not in the computer; the intellegence is in the programmer or trainer" - Poincare never suggested that machine proofs are more reliable. He found clear intutions more reliable guides to truth for both students and researchers than blind formalities can be. of course, he never faced such long techinal human proofs as we do today. Relieability is now a major motive mor mechanization. But what poincare did value about machine proofs was the making explicit of intutions. - Poincare found mechanizable proofs an indespensable supplement to live rasoning but no replacment for it. The pivotal point remains today as Poincare saw it in 1902: a machine deriving conclutions from a formal theory T does not also know the informal interpetatoins or motivatoins of T. Mathmaticians know these. - Rodrigo Ochigame, "Automated Mathematics and the Reconfiguration of Proof and Labor" - Advances in AI and ML, which have captured massive amounts of public attention and capital investment, promise to expand the auotmation of theorem proving. Formal verificatoin, once imagined to work only for rudimentary results, now seems feasible even for some of the most sophisticated results of comtemporary research. - The past and present controversies about the status of somputer-assisted proofs reflect a longstanding tension in modern mathematicas, between post-Cartesian and post-Leibnizian practical standards of proof. We should critique our reurring assumptions about automated mathematics. - (post-Cartesian and post-Leibnization Standards of Proof) - Mathmatics has never had a common notion of what establishes a valid proof. The history of mathematics is filled with failed attempts to convince all mathematitions to addopt a single and clear-cut criterion of proof. Recent proposals for computer-based formal verification are only the latest episode in this history, but perhaps they will become the exception. - A Cartesian ideal of proof: after some reflection and study, one totaly understands the proof, and can get it in one's mind all at once. - A Leibnizian ideal of proof: every step is meticulously laid out, and can be checked, line by line, in a mechanical way. - This terminologyh is from philosopher Ian Hackling. - Decartes and Gottfried Leibniz were two among many theorists of proof in the 1800s. Their contemporaries debaited about whether geometers should reject proofs by contradiction (LOOK UP MORE ABOUT THIS AND RELATE IT TO COMPUTATBILITY IN THIS PROJECT) - Neither ideal has been achieved completely, much less required, in most acutally eisting mathematics. But mathematics mixes them, or pore precisely, involves a mix of practical standars that may be seen as derivitive forms of these ideals. Both ideals repeatedly faced practical challenges, and had to be replace by more realistic standardy. - Some proofs ar etoo long to fit in one's mind "all at one". In such cases, the caresian ideal had to give way to a less strict prcticla standard. - Post-cartesian standard of long and complex proofs: after some study, one understands the proof's general strategy and each of its part, and can follow it one part at a time. - With the professionalizaoitn and speclizatoin of mathematics, some proofs become beyond the grasp of an isolated individual, and their construcion and verification may require multiple people. - After the nineteenth centrury, no individual mathematician oculd claim to know all branches of mathematics at the level of specialists. There are numerous famous examples of highly specialized proofs that demanded several years of effort at explination and persuasion. These include ultimately accepted proofs, like that of Fermat's last theorem, and as well as controversial claimed proofs, like that of the abc conjecture. Post cartesian standard of highly specialized proofs: each part of the proof is understood, after some study, by some group of trusted specialists. - Proof verification is a sophisticated social process. A claimed proof oftern has parts that can be understood by ony a few specialists in a subfield, even if its general strategy may be accessible to other professional mathematicians. In practice, the adjudication of specialized proofs relies on social institutions, such as journals, seminars, committees, degrees, awards, and symbolic markers of reputation and trust. In this regard, mathematics is not fundementially different from other fields of knowledge. - The Leibniziam ideal has also developed into different practical standares. One key transformation was the trun to modern axiomatic proofs, which wa sadvance dby Hilbert's axiomatization of geometry at the end of the nineteenth century, and later embraced by various mathematicians in the first decases of the twentieth ecentury. The members of Bourbaki are closely associated with the turn to modern axiomatics (who is are Bourbaki?). - Post-Leibnizian standard of modern axiomatic proofs: Every step can be checked, line by line, by means of strict logical deductions, and in principal can be derived from axiomatic foundations. - The key word in "in principal" .In practice, published proofs are hardly ever actually traced to the axioms. Moreover, what counds as the proper "foundations" has continually been the subject of dispute. Unitill the late nineteenth century, the foundation sf geometry were thought to be grounded in physical reality, but this idea was challenged after the formulation of non-Euclidian gemoety. In the early twoentih century, there were numerous controvercies about the foundations of alternative mathematical logics areound the world, ofr example, in the late Russian Empire (What?). Ever since ZFC became a leading candidate for a unified foundation of mathematics, the inclusion of the axiom of choice has been controversial. And as onging debates aobut univalent foundations and HoTT make clear, there are stil compelling reasons to keep questioning one's choice of axioms. - Current practices of proof reflect a complex configuration of mulitiple standars, which remain largely implicit. Mathematicians learn the standars not by reading them explicityly in textbooks, but mainly through practice. - The current configuration of proof standards: post-Leibnizian standards adjudicate the validity of a proof in principle, while post-cartesian standards adjudicate validity in practice in addition to other considerations beyond validity. - Thie post-Leibnizand standard has become the in principal since he first half of the 1900s. Mathmaticians consider it valid if they believe that every step would be valid if checked. However, post-Cartesian standards remain in practice with peer review, preprint circulation, and seminar discussion. - Proofs are deemed better when they fit cartesian standards (elegant, interesting, shrot, do not require computers) - (automation of the deductive process). Starting in the late 1960s, software systems for formal verificatoin appeared in different places, Automath, LCP, Mizar. De Bruijn, a mathematician, has recalled his firsthand experience in checking a long and repetitive proof in conbinatorics as a motivatoin for creating Automath. Mizar focused on a centrally managed database or library of mathematical papers. Many other projects followed: Isabelle, HOL, Coq, Metamath, and Lean. These projects were im part motivated by the epistemic fear that converntional mathematicl proofs, in their ever-increasing complexity and specializaiton makes them susepible to human error. Although, the philosophical motivations and axiomatic foundations and design choices have differed. Taken together, such projects have advanced a new standard of proof: - Practical standard of computer-encoded proofs: every step can be checked by a computer program and derived from the axiomatic foundations of the program; and after some study, one understands or trusts the encoding of the proven statment - This standard has both post-Leibnizian and post-Cartesian demesnstions. it is often assumed to be sufficient, becuase its post-Leibnizian demension is seen as stricter than the converntional standard of axiomatic proof in pront, which is already accepted. Some proponents of "formal" proofs tend to emphasize this post-Leibnizian dimensoin, and may wish to dliminate post-Cartesian standards involving the elusive notion of "understanding". - Computer-encoded proofs do not evade te need for human understanding. Huans must still read the code and verify that the proven statment, as incoded in the progam, actually represents or corresponds to the claim under consideration. (Use examples from my projet). Formalizatoin is ardiuos and instructive, and how has it lead to imporved comprehension in my case? - It is not controversial to accept computerized proofs as a sufficient standard. A more controversial question is wheather computer-encoded proofs should become not only sufficient but also necessary. Should math hournals require computer programs along with, or even instead of, the submitted papers? Should all theorems be denoted to conjectures untill computer-encoded proofs are avillable? Athouthg proposals of this kind have already appeared for several decasees, they have garnered more attention in recent years. One reason is that computer-encoded proofs have become realistic for increasingly sophisticated results. In 2022, a team of more than twenty reesarches succeded in formalizingng, in lean, a particulary chanllenging theorem regarding liquid vector spaces by Dustic Clausten and eter Scholze. It is also worth noting tha tht edifficulty of encoding theorems in a given system may vary depending on its axiomatic foundations. - Another part of the computerization of mathematics is the attempts to develop more atutomated methods of searching for new proofs and theorems. This is actually an older task than verification. However, these project mostly found that it is too hard. The work of "automatd theorem proving" inevitably demanded certain moments of human insight and intution. This was already recognized by reaseraches in the late 1970s, is Dick has proven in her account of the AURA project. In this sense, the boundary between automated and interactive theorem proving has always been blurry. Rther than two seperate filds, I prefer to think of one field of partially autoated practices invluving multiple variations of human guidence and interactivity. - TODO: Relate this to Lean practice in this project using automatioin! ring, simp, aesop, ect. - There is currently not any important theorem that was first proven through a deeply automated search involving limited human guidance. However, it is possible that such a theorem may appear. This raises a questoin, weill we accept the standard of proof: Potential practical standard of deeply automated proofs: one trusts the computer programs that constructed and checked the proof, even if one may not understand it at all. - For a lot of mathematicioins, understanding a proof or statment is not just a requirement for believing it, but the very point of doing mathematics. - (Critiques of recurring assumptions) the first assumption tis that computer-encoded proofs can eliminate the need for social instituitons of adjudication, such as peer review. Even in a scenario where computer-encoded proofs become required, they till demand some human involvement in the prcess of verification, at least in ensuring that the formalizaiotn actually said what they claim it does. Even more clearly, we need social instutitions to judge the importance and value of results. The assement of the value or importance of a result is tied to its percieved centrality, popularity, and difficulty. It seems a difficult task to algorithmically determine the value of a result. Not even to mention "beuty" and "originality" - Another recurring assumption is that it is feasible to formalize all mathematical knowledge. Published papers do not very closly resemble a formalizatoin, and rely on a lot of tacit knowledge and intuition. The boundaries of math as a field of knowledge are not fixed or self-evident. Each formal language or sofware system prescribes its redefinition of those boundaries, which can never include all of mathematics. The axiomatic ofundations limit what is expressible and provable within it. It is woth noting that the desire for computer based=formal verification has served to motivate the development and adoption of new foundations of mathematics. Vladimir Voevodsky acknowledged this motivation as central to his work on univalent foundations and HoTT. All formal loanges and software systems inevituably exclude some kinds of math knowledge al reder some hinds more easily expressible and legible than others. - Finally, I want to address the implicit assumptions that the growth of auomtated mathematics is driven primarily by the intellectual needs or priorities of academic mathans. Rather, this area of research has been shaped significantly by the strategic interists of the military and corporate institutions that have funded it. As sociologist Donald MacKenzie has documented, early effortts in "formal verificatoin or "program proof" emerged largely out of practical concerns about computer security, with funding from the US military, particularly the NSA. For instance, the military worried that a real computer program or operating system might not conform to its supposed mathematical model of security. By the early 1970s, the NSA percived formal verification as central to coputer security. Although military uses of computer-assisted proof have changed significantly in the fifty years since then, the US air force office of scientif research (AFOSR) still sponcers resarch in this are under its "information Assurance and Cybersecurity" Program, mentioning "interactive and automated theorem proving" as well as "formalized mathematics" among research areas that are "expected to provide valuable insights into various cybersecurity problems". - In recent years, commercial firms such as Microsoft, Google, and Meta have become growing sources of investment in automated mathematics. Unlike the military, which focuses on specific problems with more predicatble applicatoin, those firms benefit from their investments in less direct ways. They invest in the auomtation of math as part of a broader stragety of demonstrating AI capabilities in general, thus attracting public attention and capital investment. If the military tends to sponser work under the rubric of cibersecurity, those firms have branded such work more often as AI, focusing lately on LLMs and deep learning. Unsuprisingly, PR teams and corporate sponseored researchers deploy hyperbolic language to publicize their work. FOr example, by framing their research as an effort to "create an automatic mathematician" (google). Or even asking sensationally "Is human-led mathematics over?" (Meta). It remains to be seen whether academic mathematician siwll embrace or refuse the modus operandi of hype-driven stock market snad venture capital.
# Formalization of DFA Minimization in Lean 4

This repository contains a formalization of the minimization of deterministic finite automata (DFAs) in the Lean 4 theorem prover.

# Why Formalize Mathmatics

Mathematics is typically communicated in precise but informal language, where definitions and proofs are written for human readers and leave many steps implicit. This style has proven powerful, but it also has a limitation: the correctness of a proof ultimately depends on social verification. Mathematicians check arguments themselves, discover errors, and fill in gaps. As proofs grow larger and more complex, this informal process becomes fragile.

Mathematicians responded to this problem with mathematical formalization, where definitions, statements, and proofs are represented inside a formal system with precise syntax and semantics. In a formal setting, a theorem is a syntactic object: a derivation from axioms and previously proved results, where every step is justified by an explicit rule. This yields a notion of proof that is not mediated by interpretation, but by a mechanical and machine-checkable standard. Instead of relying on “it is clear that…”, a formal proof must make every dependency explicit, sometimes at the cost of verbosity, but in exchange for guaranteed correctness.

Historically, fully formal proofs were too labor-intensive to be a realistic replacement for ordinary mathematical writing. This is the problem that interactive theorem provers (ITPs) were created to solve. An ITP is software in which a user incrementally constructs a proof while the system checks that each step follows from the axioms and inference rules of the underlying logic. Modern provers provide powerful automation high-level tactics so that users can write proofs at a reasonably high level of abstraction. At the same time, they are engineered around a trusted kernel which checks proofs, and everything else is treated as a convenience layer whose output is still validated by the kernel.

## Lean 4 and Mathlib
TODO - explain the landscape of mathlib

Lean 4 is a modern proof assistant that is both an ITP and a functional programming language based on dependent type theory. This combination is particularly well suited to formalizing mathematics that has an algorithmic component. In Lean, one can define mathematical objects, state theorems about them, and also write executable functions that compute with them. A proof about an algorithm can therefore refer to the actual definition being executed, not to an informal description that might subtly diverge from an implementation.

Large-scale formalization is made feasible by Lean’s community library, mathlib. Mathlib provides a broad foundation of definitions and theorems across many mathematical domains. In traditional mathematics, large projects are limited by the amount of trust required between collaborators—each participant must rely on the correctness of others’ work. In a formal library, contributions are checked by the kernel, so the “cost of trust” is reduced. This enables thousands of contributors to build a coherent, machine-checked body of mathematics that future work can extend.

## Machine checked algorithms

An application of proof assistants is the verification of algorithms against mathematical specifications. In an ITP like Lean, one can define a specification of correctness, define an algorithm as a function, then prove that the algorithm satisfies the specification for all inputs. This allows one to verify that an algiorithm is not only correct, but also satifies stonger properties such as always producing a canonical result (if you define some notion of equivalence). 

## Computability 

Formal verification also brings the relationship between mathematics and computation into view. In traditional classical mathematics, it is common to prove that an object exists without giving a procedure to construct it. In contrast, in constructive mathematics, an existence proof is expected to provide a method of construction. Proof assistants make this distinction concrete because definitions can be executed and theorems can carry computational content.
Lean enforces that definitional computation is well behaved: functions are total (they must terminate) and deterministic (the same input produces the same output). As a result, implementing an algorithm that constructs an object can be viewed as giving computational evidence of existence. When paired with a proof of correctness, the algorithm becomes a constructive witness: not only does a desired object exist, but we can acutally compute it. 

## Table of Contents

- [What is Lean?](#what-is-lean)
- [What is Mathlib?](#what-is-mathlib)
- [Motivation](#motivation)
- [What is a DFA?](#what-is-a-dfa)
- [Minimal DFAs](#minimal-dfas)
- [DFA Morphisms](#dfa-morphisms)
- [Computability](#computability)
- [Project Structure](#project-structure)
- [Current Developments](#current-developments)

---

## What is Lean?

Lean 4 is an interactive theorem prover (ITP) and programming language.

Unlike traditional programming languages, Lean is functional and based on dependent type theory, which allows types to depend on values. This enables Lean to serve both as a programming language and a proof assistant.

Lean uses the Curry–Howard correspondence, where some types are interpreted as propositions, and terms of those types are interpreted as proofs.

Lean stands out among ITPs for its focus on formalizing mathematics and its strong community tooling.

---

## What is Mathlib?

Mathlib is the mathematical library for Lean, containing over 1.5 million lines of formalized mathematics. It is the largest unified mathematical library for any theorem prover. It covers algebra, analysis, number theory, and a small amount of automata theory.

---

## Motivation

Mathlib already contains a definition of DFAs and some basic theorems about them (such as the pumping lemma), but it does not contain definitions or theorems related to DFA accessibility, morphisms, or minimization.

This project aims to fill that gap by providing a formalization of these concepts.

---

## What is a DFA?

A **deterministic finite automaton** (DFA) is a finite-state machine that accepts or rejects a given string of symbols by running through a sequence of states.

Every DFA is defined over a finite **alphabet**, which is a set of letters. When evaluated on a word over this alphabet, the DFA either accepts or rejects that word.

The figure below is a state diagram of a particular DFA defined over the alphabet {a, b}:

*[Insert Figure 1]*

This DFA has two states, labeled S₁ and S₂. The unlabeled arrow pointing to S₁ indicates that it is the **start state**, and the double circle around S₂ indicates that it is an **accepting state**. The labeled arrows are **state transitions**, and it is required that every state has exactly one outgoing arrow for each character in the alphabet.

When evaluating a word, a DFA begins at the designated start state, then follows the arrow labeled by the first letter of the word. Then, it follows the arrow labeled by the second letter of the word, and so on until you reach the end of the word. If the state it ends on is an accepting state, then the DFA accepts the word; otherwise, it rejects.

For example, evaluating the word "bab" on the DFA above:
1. Begin in state S₁
2. Read "b" → transition to S₁
3. Read "a" → transition to S₂
4. Read "b" → transition to S₂

Since S₂ is an accepting state, this DFA accepts the word "bab".

The set of words that a DFA accepts is called the **language** of that DFA.

You might notice that the language of this DFA is the set of all words that contain an odd number of "a"s (and any number of "b"s).

### Lean Definition

Mathlib contains a formal definition of a DFA as a structure type:

```lean
structure DFA (α : Type u) (σ : Type v) where
  step : σ → α → σ
  start : σ
  accept : Set σ
```

This structure is parameterized by two input types, `α` and `σ`, which represent the alphabet and set of states, respectively. It has three fields:
- `step : σ → α → σ` — the transition function, which encodes the "arrows" between states
- `start : σ` — a single designated start state
- `accept : Set σ` — a set of accepting states

Mathlib also defines DFA evaluation as follows:

```lean
/-- `M.evalFrom s x` evaluates `M` with input `x` starting from the state `s`. -/
def evalFrom (M : DFA α σ) (s : σ) : List α → σ :=
  List.foldl M.step s

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
def eval (M : DFA α σ) : List α → σ :=
  M.evalFrom M.start
```

Mathlib provides a function that returns the language accepted by a DFA from a particular state. Here, `Language α` is just a wrapper for `Set (List α)`:

```lean
/-- `M.acceptsFrom s` is the language of `x` such that `M.evalFrom s x` is an accept state. -/
def acceptsFrom (s : σ) : Language α := {x | M.evalFrom s x ∈ M.accept}

/-- `M.accepts` is the language of `x` such that `M.eval x` is an accept state. -/
def accepts : Language α := M.acceptsFrom M.start
```

Let's test out some of these functions on our simple DFA from Figure 1. First, we define the state and alphabet types:

```lean
inductive α₁ : Type
  | a
  | b
deriving DecidableEq, Fintype

inductive σ₁ : Type
  | s₁
  | s₂
deriving DecidableEq, Fintype
```

Now, we can define our DFA from Figure 1 over these types:

```lean
def M₁ : DFA α₁ σ₁ where
  step (s : σ₁) (x : α₁) :=
    match s, x with
    | σ₁.s₁, α₁.a => σ₁.s₂  -- (s₁, a) goes to s₂
    | σ₁.s₁, α₁.b => σ₁.s₁  -- loop on b in s₁
    | σ₁.s₂, α₁.a => σ₁.s₁  -- (s₂, a) goes to s₁
    | σ₁.s₂, α₁.b => σ₁.s₂  -- loop on b in s₂
  start := σ₁.s₁
  accept := {σ₁.s₂}
```

We can use Lean's `#eval` to see the result of evaluating the word "bab" on this DFA:

```lean
#eval M₁.eval [α₁.b, α₁.a, α₁.b]
```

This prints `σ₁.s₂` to the Infoview, which is an accepting state.

### Another DFA Example

For a slightly more complex example, consider this DFA, again defined over the alphabet {a, b}:

*[Insert Figure 2]*

The language of this DFA is the set of all words with an odd number of "a"s *and* an odd number of "b"s.

Now, imagine that you are halfway through evaluating a word for this DFA, and you are currently at state S₂. What does the rest of the word have to look like for the whole word to be accepted? The rest of the word must contain an even number of "a"s and an odd number of "b"s.

| State | Required suffix language |
|-------|--------------------------|
| S₁ | Odd "a"s and odd "b"s |
| S₂ | Even "a"s and odd "b"s |
| S₃ | Odd "a"s and even "b"s |
| S₄ *(accepting)* | Even "a"s and even "b"s |

This idea of the language accepted *from a particular state* is fundamental in algorithms that minimize DFAs.

---

## Minimal DFAs

Multiple DFAs can accept the same language. For example, here is another DFA that also accepts the language of words with an odd number of "a"s and an odd number of "b"s:

*[Insert Figure 3]*

Given a DFA, one may ask if this DFA is **minimal** for the language it accepts. For now, let's call a DFA "minimal" if it has the fewest states of all DFAs recognizing the same language. Later, we will define a stronger notion of minimality based on DFA morphisms.

This DFA is not minimal, and this can be illustrated by considering the language accepted from each state:

| State | Required suffix language |
|-------|--------------------------|
| S₁ or S₅ | Odd "a"s and odd "b"s |
| S₂ or S₆ | Even "a"s and odd "b"s |
| S₃ or S₇ | Odd "a"s and even "b"s |
| S₄ or S₈ *(accepting)* | Even "a"s and even "b"s |

When the language accepted from two states is the same (for example, S₁ and S₅), the DFA is not minimal because those states could be collapsed into a single state. Conversely, if the language accepted from each state is unique, as in Figure 2, the DFA is minimal.

### A Minimization Algorithm

DFA minimization is the problem of, given a DFA, creating a minimal DFA that accepts the same language.

We will minimize the DFA in Figure 3, again considering the languages accepted from each state (see table above).

We create a relation on the states of Figure 3 called the **Nerode equivalence**. Two states are Nerode-equivalent if and only if the language accepted from each state is the same. In this case:
- States S₁ and S₅ are Nerode-equivalent
- States S₂ and S₆ are Nerode-equivalent
- States S₃ and S₇ are Nerode-equivalent
- States S₄ and S₈ are Nerode-equivalent

```lean
def nerodeEquiv (M : DFA α σ) (s₁ s₂ : σ) : Prop :=
  M.acceptsFrom s₁ = M.acceptsFrom s₂
```

In our minimized DFA, the set of states will be the set of equivalence classes of the Nerode equivalence relation. In this case, we have four equivalence classes:
- {S₁, S₅}
- {S₂, S₆}
- {S₃, S₇}
- {S₄, S₈}

```lean
/-- For a DFA `M`, `M.toNerodeDFA` is a DFA whose state-space is the
quotient of `M`'s by the Nerode equivalence. -/
def toNerodeDFA (M : DFA α σ) : DFA α (Quotient M.nerodeEquiv) where
  step (s' : Quotient M.nerodeEquiv) (a : α) :=
    Quotient.lift
      (fun s : σ ↦ ⟦M.step s a⟧)
      (by intros s₁ s₂ h; simp; apply nerodeEquiv.step; apply h) s'
  start := ⟦M.start⟧
  accept := {⟦q⟧ | q ∈ M.accept}
```

We designate the start state as the Nerode equivalence class containing the original start state (in this case, {S₁, S₅}), and we designate the accepting states as any Nerode equivalence classes containing an accepting state (in this case, {S₄, S₈}).

Notice how, if you are in state S₁ or S₅, seeing an "a" will always map to state S₂ or S₆. Seeing a "b" will always map to state S₃ or S₇. In fact, members of a Nerode equivalence class always transition to the same Nerode equivalence class on the same input. In this way, we say that the Nerode equivalence **preserves the transition function**. Because of this, we can define the transition function of the minimized DFA:

| State | Letter | Destination |
|-------|--------|-------------|
| {S₁, S₅} *(start)* | a | {S₂, S₆} |
| {S₁, S₅} | b | {S₃, S₇} |
| {S₂, S₆} | a | {S₁, S₅} |
| {S₂, S₆} | b | {S₄, S₈} *(accept)* |
| {S₃, S₇} | a | {S₄, S₈} *(accept)* |
| {S₃, S₇} | b | {S₁, S₅} |

Here is the resulting minimal automaton—notice how it is the same as the DFA in Figure 2:

*[Insert Figure 4]*

### A Problem with the Minimization Algorithm

The algorithm above often provides a minimal automaton, but only if the starting DFA is **accessible**.

A state of a DFA is **accessible** if there is some word that reaches that state. A DFA is **accessible** if every state is accessible.

```lean
/-- A predicate on states of a `DFA` asserting that there exists a word
`w` such that `M.eval w` equals that state. -/
def IsAccessibleState (M : DFA α σ) (s : σ) : Prop :=
  ∃ w : List α, M.eval w = s

/-- A typeclass on `DFA`s asserting that every state is accessible. -/
class Accessible (M : DFA α σ) where
  allAccessible (s : σ) : M.IsAccessibleState s
```

For example, consider this DFA, again accepting the language of words with odd "a"s and odd "b"s, but with an inaccessible state S₅:

*[Insert Figure 5]*

The language accepted from state S₅ is unique: any number of "b"s, followed by one "a", followed by an even number of "a"s and an even number of "b"s.

This adds another Nerode equivalence class, so the algorithm above would not fully minimize the DFA.

To reconcile this, we can update our minimization algorithm to trim away inaccessible states before (or after) collapsing Nerode-equivalent states:

```lean
/-- Given a `M : DFA α σ`, `M.toAccessible` is `M` but with all
the non-accessible states removed. -/
def toAccessible (M : DFA α σ) : DFA α {s // M.IsAccessibleState s} where
  step s a := ⟨M.step s.val a, by
    obtain ⟨x, hx⟩ := s.prop
    use x ++ [a]
    simp [hx]⟩
  start := ⟨M.start, by use []; simp⟩
  accept := {s | s.val ∈ M.accept}

/-- The minimal DFA accepting the same language as `M`. -/
@[simp] def minimize : DFA α (Quotient M.toAccessible.nerodeEquiv) :=
  M.toAccessible.toNerodeDFA
```

---

## DFA Morphisms

This project builds on the Mathlib implementation of DFAs with a notion of DFA morphisms.

A **DFA morphism** is a function between the state types of two DFAs that preserves the start state, accepting states, and the transition function.

In Lean, this is implemented as a structure parameterized by two DFAs (which must be defined over the same alphabet) with four fields. The first field, `toFun`, is the underlying function between the state types, while the other three fields are proofs that the function preserves the required structure.

We define notation such that `M →L N` is the type of morphisms from `M` to `N`:

```lean
structure Hom (M : DFA α σ₁) (N : DFA α σ₂) where
  toFun : σ₁ → σ₂
  map_start : toFun M.start = N.start
  map_accept : ∀ q : σ₁, (q ∈ M.accept) ↔ (toFun q ∈ N.accept)
  map_step : ∀ (q : σ₁) (w : List α),
    toFun (M.evalFrom q w) = N.evalFrom (toFun q) w

infixr:25 " →L " => Hom
```

We prove in `Hom.pres_lang` that DFA morphisms preserve the accepted language. That is, if there exists a morphism from a DFA `M` to a DFA `N`, then `M` and `N` accept the same language.

We say that a DFA morphism is **surjective** if and only if its underlying function is surjective.

An **equivalence of DFAs** is a bijective morphism, notated `M ≃L N`.

### Minimality via Morphisms

Using this notion of DFA equivalence, we can define a more precise specification of DFA minimality.

We define a preorder on DFAs that are defined over the same alphabet:

```lean
/-- `M ≤ N` iff there is a surjective morphism `N ↠ M`. -/
def AccessibleLE (M : DFA α σ₁) [Accessible M] (N : DFA α σ₂) [Accessible N] : Prop :=
  Nonempty (N ↠ M)
```

This captures the idea that `M ≤ N` if and only if there is some structure-preserving function that *collapses* the states of `N` to those of `M`.

A **minimal DFA**, then, is a DFA that is minimal in this order:

```lean
/-- An accessible DFA is minimal if every smaller accessible DFA is equivalent to it. -/
def IsMinimal (M : DFA α σ₁) [Accessible M] : Prop :=
  ∀ {σ₂ : Type*} (N : DFA α σ₂) [Accessible N] (_ : N ≤ M),
    Nonempty (M ≃ₗ N)
```

We prove that the DFA returned by our minimization algorithm is minimal:

```lean
/-- `M.minimize` is minimal by our partial order defined by the existence of surjective
DFA morphisms. -/
theorem minimize_isMinimal : M.minimize.IsMinimal := by
  exact M.toAccessible.toNerodeDFA_isMinimal
```

---

## Computability

The formalization presented above is not sufficient to actually *compute* a minimal DFA. We defined the Nerode equivalence as a proposition, but what we want is a function `state → state → Bool` that actually computes, in a finite amount of time, whether two states are Nerode-equivalent. Similarly, we need a function that *decides* if a state is accessible, rather than simply defining what an accessible state is propositionally.

Writing these computable functions, and proving that they are correct, makes up the bulk of this project. In fact, much of the mathematical content of DFA minimization only becomes relevant in this computable setting.

### Computable Accessibility Algorithm

Recall the definition of an accessible state:

```lean
/-- A predicate on states of a `DFA` asserting that there exists a word
`w` such that `M.eval w` equals that state. -/
def IsAccessibleState (M : DFA α σ) (s : σ) : Prop :=
  ∃ w : List α, M.eval w = s
```

The set of words over the alphabet is infinite, so how does one test, in a finite amount of time, whether any of those words reaches the state? We make use of an important theorem:

> **Theorem:** If a state is accessible, then it is accessed by some word of length at most |σ| (the number of states).

```lean
/-- Given that the set of states is finite, every accessible state is reachable by a
word of length at most the number of states. -/
theorem exists_short_access_word (s : σ) {w : List α}
    (hw : M.eval w = s) :
    ∃ v : List α, v.length ≤ Fintype.card σ ∧ M.eval v = s := by
  ...
```

I will not explain the proof fully here, but it makes use of strong induction and the fact that, if a path through a DFA is longer than the number of states in the DFA, then there must be a repeated state in that path.

Using this theorem, we can now decide if a state is accessible by checking only the finite set of words of length at most |σ|.

### Computable Nerode Equivalence

To make the full minimization pipeline computable, we need a computable algorithm that decides if two states are Nerode-equivalent.

Recall that two states are Nerode-equivalent if and only if the languages accepted from those states are equal. We again have the problem that, in general, these languages are infinite sets of words, so we must use a theorem to reduce this to a finite check:

> **Theorem:** Two states are Nerode-equivalent if and only if, for all words of length at most |σ|, evaluating the word from those states leads to the same acceptance outcome.

The proof of this theorem is the most involved in the project. I will explain it here at a high level.

#### Bounded Nerode Equivalence

First, we formalize the notion of two states defining the same language for words up to some length *n*:

```lean
/-- A word indistinguishes two states if evaluating from them leads to the same acceptance
outcomes. -/
private def Indist (M : DFA α σ) (w : List α) (s₁ s₂ : σ) : Prop :=
  (M.evalFrom s₁ w ∈ M.accept) ↔ (M.evalFrom s₂ w ∈ M.accept)

/-- The bounded Nerode equivalence at level `n`: two states are equivalent if they are
indistinguishable by words of length ≤ `n`. -/
def boundedNerode (M : DFA α σ) (n : ℕ) (s₁ s₂ : σ) : Prop :=
  ∀ w : List α, w.length ≤ n → M.Indist w s₁ s₂
```

We can now state our theorem as:

> Two states are Nerode-equivalent if and only if they are *n*-bounded-Nerode-equivalent for *n* = |σ|.

#### Monotonicity of Bounded Nerode Equivalence

In order to prove the above theorem, we establish that if *n* ≤ *m*, then if two states are *m*-bounded-Nerode-equivalent, they are also *n*-bounded-Nerode-equivalent:

```lean
/-- Monotonicity of bounded Nerode. -/
private theorem boundedNerode_mono {n m : ℕ} (hle : n ≤ m) :
    M.boundedNerode m ≤ M.boundedNerode n := by
  simp [Setoid.le_def, boundedNerode]
  intros s₁ s₂ h₁ w h₂
  apply h₁
  omega
```

This theorem also implies that the *n*-bounded-Nerode relation partitions the set of states into a number of equivalence classes that is increasing in *n*.

#### Stabilization of Bounded Nerode Equivalence

We say that the bounded Nerode equivalence **stabilizes** at *n* if *n*-bounded-Nerode-equivalence is the same relation as (*n* + 1)-bounded-Nerode-equivalence. We prove that if the bounded Nerode equivalence stabilizes at *n*, then it equals the bounded Nerode equivalence at *m* for all *m* ≥ *n*, and thus equals the unbounded Nerode equivalence:

```lean
/-- If bounded Nerode stabilizes at `n`, then it equals the Nerode equivalence. -/
private lemma boundedNerode_stable_eq_nerode {n : ℕ}
    (heq : M.boundedNerode n = M.boundedNerode (n + 1)) :
    M.boundedNerode n = M.nerodeEquiv := by
  ...
```

We can now say that, for any *n*, (*n* + 1)-bounded-Nerode-equivalence is either *strictly* finer than *n*-bounded-Nerode-equivalence (and thus partitions the set of states into *strictly* more equivalence classes), or it equals the full Nerode equivalence.

Because an equivalence relation cannot partition a set into more equivalence classes than there are elements in the set, the bounded Nerode equivalence at *n* = |σ| must be stabilized and thus equals the unbounded Nerode equivalence.

This allows us to decide if two states are Nerode-equivalent by checking only the finite set of words of length at most |σ|, making our relation computable:

```lean
/-- Decidability instance for testing if two states of a finite DFA are
Nerode-equivalent. -/
instance nerode_decidable : DecidableRel M.nerodeEquiv := by
  intros s₁ s₂
  apply decidable_of_decidable_of_iff (M.boundedNerode_iff_nerode s₁ s₂)
```

---

## Project Structure

The formalization is organized as follows:

| File | Contents |
|------|----------|
| `MyProject/DFA/Hom.lean` | DFA morphisms, surjections, equivalences, and the preorder on DFAs |
| `MyProject/DFA/Accessible.lean` | Accessibility predicate, `toAccessible`, and decidability |
| `MyProject/DFA/Nerode.lean` | Nerode equivalence, bounded equivalence, and stabilization proofs |
| `MyProject/DFA/Minimize.lean` | The minimization algorithm and correctness proofs |
| `MyProject/DFA/Fin.lean` | The `Fin` typeclass for computable DFAs |

---

## Current Developments

I initially intended for this project to be a contribution to Mathlib, and I recently made a post on the Lean 4 Zulip channel about it:

[Automata Theory Contribution – Lean Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Automata.20Theory.20Contribution/with/562817136)

However, I was pointed to another community project called **CSLib**, which focuses more directly on automata theory. This project uses different definitions of DFAs, but (like Mathlib) it lacks a formalization of DFA morphisms, accessibility, and minimization. I am currently refactoring this project to use the CSLib definitions and preparing a pull request to CSLib.
