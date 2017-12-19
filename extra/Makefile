all:
	cat bash_completion_forest | sed "s@%forest_main_file%@"${PWD}"/../front-end/forest.cpp@" | sudo tee /etc/bash_completion.d/forest
	echo 'autoload -U +X compinit && compinit' >> ~/.zshrc
	echo 'autoload -U +X bashcompinit && bashcompinit' >> ~/.zshrc
	echo 'source /etc/bash_completion.d/forest' >> ~/.zshrc
