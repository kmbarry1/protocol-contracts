
certora: FORCE
	PATH=${PWD}/certora:${PATH} certoraRun \
		--solc ~/.solc-select/artifacts/solc-0.8.7 \
		--solc_evm_version london \
		contracts/zevm/ZRC20.sol \
		--verify ZRC20:certora/ZRC20.spec \
		$(if $(rule),--rule $(rule),)

FORCE:
