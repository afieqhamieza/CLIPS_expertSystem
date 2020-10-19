;;;***************************
;;;* DEFTEMPLATE DEFINITIONS *
;;;***************************

(deftemplate rule 
   (multislot if)
   (multislot then))

;;;**************************
;;;* INFERENCE ENGINE RULES *
;;;**************************

(defrule propagate-goal ""
   (goal is ?goal)
   (rule (if ?variable $?)
         (then ?goal ? ?value))
   =>
   (assert (goal is ?variable)))
   
(defrule ask-questions ""
	(declare (salience 10))
	(legalanswers ? $?answers)
	?f1 <- (goal is ?variable)
	?f2 <- (question ?variable ? ?text)
	=>
	(retract ?f1)
	(format t "%s " ?text)
	(printout t ?answers " ")
	(bind ?reply (read))
	(if (member$ (lowcase ?reply) ?answers)
		then (assert (variable ?variable ?reply))
			(retract ?f2)
		else (assert (goal is ?variable))))

(defrule goal-satified ""
   (declare (salience 30))
   ?f <- (goal is ?goal)
   (variable ?goal ?value)
   (answer ? ?text ?goal)
   =>
   (retract ?f)
   (format t "%s%s%n" ?text ?value))

(defrule remove-rule-no-match ""
   (declare (salience 20))
   (variable ?variable ?value)
   ?f <- (rule (if ?variable ? ~?value $?))
   =>
   (retract ?f))

(defrule modify-rule-match ""
   (declare (salience 20))
   (variable ?variable ?value)
   ?f <- (rule (if ?variable ? ?value and $?rest))
   =>
   (modify ?f (if ?rest)))

(defrule rule-satisfied ""
   (declare (salience 20))
   (variable ?variable ?value)
   ?f <- (rule (if ?variable ? ?value)
               (then ?goal ? ?goal-value))
   =>
   (retract ?f)
   (assert (variable ?goal ?goal-value)))

(defrule ask-question-no-legalvalues ""
   (declare (salience 10))
   (not (legalanswers $?))
   ?f1 <- (goal is ?variable)
   ?f2 <- (question ?variable ? ?text)
   =>
   (retract ?f1 ?f2)
   (format t "%s " ?text)
   (assert (variable ?variable (read))))

(defrule ask-question-legalvalues ""
   (declare (salience 10))
   (legalanswers ? $?answers)
   ?f1 <- (goal is ?variable)
   ?f2 <- (question ?variable ? ?text)
   =>
   (retract ?f1)
   (format t "%s " ?text)
   (printout t ?answers " ")
   (bind ?reply (read))
   (if (member (lowcase ?reply) ?answers) 
     then (assert (variable ?variable ?reply))
          (retract ?f2)
     else (assert (goal is ?variable))))

;;;***************************
;;;* DEFFACTS KNOWLEDGE BASE *
;;;***************************

(deffacts knowledge-base 
   (goal is type.animal)
   (legalanswers are yes no)
   
   
   
   ;--- R1 ---
   (rule (if hair is yes)
   		(then group is mammal))
   (rule	(if hair is no)
   		(then group is not-mammal))
   (question hair is "does your animal has hair?")
   
   ;--- R2 ---
   (rule (if group is not-mammal and
   			milk-giver is yes)
   		(then group is mammal))
   (rule	(if group is not-mammal and 
   			milk-giver is no)
   		(then group is not-mammal))
   (question milk-giver is "Does the animal gives milk?")
   
   ;--- R3 ---
   (rule (if group is not-mammal and
   			has-feathers is yes)
   		(then group is bird))
   (rule	(if group is not-mammal and 
   			has-feathers is no)
   		(then group is not-bird))
   (question has-feathers is "Does it has feathers?")
   
   ;--- R4 ---
   (rule	(if group is not-bird and
   			flies is yes )
   		(then class is flies))
   (rule	(if group is not-bird and
   			flies is no )
   		(then class is dont-fly))
   (question flies is "Does the animal flies?")
   
   (rule (if class is flies and 
   			egg-layer is yes)
   		(then group is bird))
   (rule (if class is flies and 
   			egg-layer is no)
   		(then group is not-bird))
   (question egg-layer is "Does the animal lay eggs?")
   		
   ;--- R5 ---
   (rule	(if group is mammal and
   			meat-eater is yes)
   		(then sub-group is carnivore))
   (rule	(if group is mammal and
   			meat-eater is no)
   		(then sub-group is not-carnivore))
   (question meat-eater is "Does it eats meat?")
   
   ;--- R6 ---
   (rule	(if sub-group is not-carnivore and
   			pointed-teeth is yes)
   		(then class is pointed-teeth))
   (rule	(if sub-group is not-carnivore and
   			pointed-teeth is no)
   		(then sub-group is not-carnivore))
   (question pointed-teeth is "Does the animal has pointed-teeth?")
   
   (rule	(if class is pointed-teeth and
   			claws is yes)
   		(then class is claws))
   (rule	(if class is pointed-teeth and
   			claws is no)
   		(then sub-group is not-carnivore))
   (question claws is "Does the animal has claws?")
   
   (rule	(if class is claws and
   			forward-eyes is yes)
   		(then sub-group is carnivore))
   (rule	(if class is claws and
   			forward-eyes is no)
   		(then sub-group is not-carnivore))
   (question forward-eyes is "Does the animal has forward-eyes?")
   
   ;--- R7 ---
   (rule	(if sub-group is not-carnivore and
   			has-hooves is yes)
   		(then sub-group is ungulate))
   (rule	(if sub-group is not-carnivore and
   			has-hooves is no)
   		(then sub-group is not-ungulate))
   (question has-hooves is "Does it has hooves?")
   		
   ;--- R8 ---
   (rule	(if sub-group is not-ungulate and
  			cud-chewer is yes)
   		(then sub-group is ungulate))
   (rule	(if sub-group is not-ungulate and
  			cud-chewer is no)
   		(then sub-group is not-ungulate))  
   (question cud-chewer is "Is the animal a cud chewer?") 
   		
   ;--- R9 ---
   (rule (if sub-group is carnivore and 
  			tawny-color is yes)
  		(then class is tawny-color))
   (rule (if sub-group is carnivore and 
  			tawny-color is no)
  		(then type.animal is not-tiger-nor-cheetah))
   (question tawny-color is "Does the animal has tawny-color?")
  
   (rule	(if class is tawny-color and
   			dark-spot is yes)
   		(then type.animal is cheetah))
   (rule	(if class is tawny-color and
   			dark-spot is no)
   		(then class is no-dark-spot))
   (question dark-spot is "Does the animal has dark spots?")
   
   ;--- R10 ---
   (rule	(if class is no-dark-spot and 
   			black-stripes is yes)
   		(then type.animal is tiger))
   (rule	(if class is no-dark-spot and 
   			black-stripes is no)
   		(then type.animal is not-tiger))
   (question black-stripes is "Does the animal has black stripes?")
   		
   ;--- R11 ---
   (rule	(if sub-group is ungulate and 
   			long-legs is yes)
   	 	(then class is long-legs))
   (rule	(if sub-group is ungulate and 
   			long-legs is no)
   	 	(then class is no-long-legs))
   (question long-legs is "does the animal has long legs?")
   
   (rule (if class is long-legs and
   			long-neck is yes)
   		(then class is long-neck))
   (rule	(if class is long-legs and 
   			long-neck is no)
   		(then type.animal is not-girrafe))
   (question long-neck is "Does the animal has a long neck?")
   
   (rule (if class is long-neck and
   			dark-spots is yes)
   		(then type.animal is girrafe))
   (rule (if class is long-neck and
   			dark-spots is no)
   		(then type.animal is not-girrafe))
   (question dark-spots is "Does it has dark spots?")
   
   ;--- R12 ---
   (rule	(if class is no-long-legs and
   			white-colour is yes)
   		(then class is white-colour))
   (rule	(if class is no-long-legs and
   			white-colour is no)
   		(then type.animal is not-girrafe-nor-zebra))
   (question white-colour is "Is the animal white colour?")
   
   (rule	(if class is white-colour and
   			black-stripes is yes)
   		(then type.animal is zebra))
   (rule	(if class is white-colour and
   			black-stripes is no)
   		(then type.animal is not-girrafe-nor-zebra))
   (question black-stripes is "Does the animal has black stripes?")
   
   ;--- R15 ---
   (rule (if group is bird and
   			flies is yes )
   		(then type.animal is albatross))
   (rule (if group is bird and
   			flies is no)
   		(then class is dont-fly))
   (question flies is "Does the animal flies?")
   
   ;--- R13 ---
   (rule (if class is dont-fly and
   			long-legs is yes)
   		(then class is long-legs))
   (rule (if class is dont-fly and
   			long-legs is no)
   		(then class is no-long-legs))
   (question long-legs is "Does the animal has long legs?")
   
   (rule	(if class is long-legs and
   			long-neck is yes)
   		(then class is long-neck))
   (rule	(if class is long-legs and
   			long-neck is no)
   		(then type.animal is not-ostrich))
   (question long-neck is "Does the animal has a long neck?")
   
   (rule	(if class is long-neck and 
   			black-white is yes)
   		(then type.animal is ostrich))
   (rule	(if class is long-neck and 
   			black-white is no)
   		(then type.animal is not-ostrich))
   (question black-white is "Is the animal black and white?")
   		
   ;--- R14 ---
   (rule	(if class is no-long-legs and 
   			swims is yes)
   		(then class is swims))
   (rule	(if class is no-long-legs and 
   			swims is no)
   		(then type.animal is not-penguin))
   (question swims is "Does the animal swims?")
   
   (rule	(if class is swims and
   			black-white is yes)
   		(then type.animal is penguin))
   (rule	(if class is swims and 
   			black-white is no)
   		(then type.animal is not-penguin))
   (question black-white is "Is the animal black and white?")
   		


   (answer is "I think your animal is a " type.animal))

   
   
   
   
   
   
   
   
   
   
   
   
   
   
