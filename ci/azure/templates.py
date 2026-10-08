"""Azure ARM resources. No cloud operations at import time."""
from common import IMAGE, tags

ARM = 'https://management.azure.com'


def rg_id(state, kind):
    return f"/subscriptions/{state['subscription']}/resourceGroups/{state['names'][kind + '_rg']}"


def workflow(state):
    uri = ARM + rg_id(state, 'compute') + '?api-version=2021-04-01'
    def http(method):
        return {'type': 'Http', 'inputs': {
            'uri': uri, 'method': method,
            'authentication': {'type': 'ManagedServiceIdentity', 'audience': ARM + '/'},
            'retryPolicy': {'type': 'fixed', 'count': 8, 'interval': 'PT30S'}},
            'operationOptions': 'DisableAsyncPattern'}
    probe, delete = http('GET'), http('DELETE')
    probe['runAfter'] = {}
    delete['runAfter'] = {'Wait_until_deadline': ['Succeeded']}
    return {'location': state['region'], 'tags': tags(state['job_id']),
            'identity': {'type': 'SystemAssigned'}, 'properties': {
                'state': 'Enabled', 'definition': {
                    '$schema': 'https://schema.management.azure.com/providers/Microsoft.Logic/schemas/2016-06-01/workflowdefinition.json#',
                    'contentVersion': '1.0.0.0',
                    'triggers': {'manual': {'type': 'Request', 'kind': 'Http', 'inputs': {'schema': {}}}},
                    'actions': {'Verify_scope': probe,
                                'Wait_until_deadline': {'type': 'Wait',
                                    'inputs': {'until': {'timestamp': state['deadline']}},
                                    'runAfter': {'Verify_scope': ['Succeeded']}},
                                'Delete_compute_group': delete}, 'outputs': {}}}}


def compute_template(state):
    resources = []
    def resource(kind, name, properties, dependencies=(), api='2024-05-01', **extra):
        resources.append({'type': kind, 'apiVersion': api, 'name': name,
                          'location': state['region'], 'tags': tags(state['job_id']),
                          'dependsOn': list(dependencies), 'properties': properties, **extra})
    def rid(kind, name):
        return f"[resourceId('{kind}', '{name}')]"
    nsg = rid('Microsoft.Network/networkSecurityGroups', 'audit-nsg')
    vnet = rid('Microsoft.Network/virtualNetworks', 'audit-vnet')
    pip = rid('Microsoft.Network/publicIPAddresses', 'audit-ip')
    nic = rid('Microsoft.Network/networkInterfaces', 'audit-nic')
    resource('Microsoft.Network/networkSecurityGroups', 'audit-nsg', {'securityRules': [{
        'name': 'DenyAllInbound', 'properties': {'priority': 100, 'direction': 'Inbound',
        'access': 'Deny', 'protocol': '*', 'sourcePortRange': '*', 'destinationPortRange': '*',
        'sourceAddressPrefix': '*', 'destinationAddressPrefix': '*'}}]})
    resource('Microsoft.Network/virtualNetworks', 'audit-vnet', {
        'addressSpace': {'addressPrefixes': ['10.89.0.0/24']},
        'subnets': [{'name': 'audit', 'properties': {'addressPrefix': '10.89.0.0/24',
             'defaultOutboundAccess': False, 'networkSecurityGroup': {'id': nsg}}}]}, [nsg])
    resource('Microsoft.Network/publicIPAddresses', 'audit-ip', {
        'publicIPAllocationMethod': 'Static', 'publicIPAddressVersion': 'IPv4'}, sku={'name': 'Standard'})
    resource('Microsoft.Network/networkInterfaces', 'audit-nic', {
        'networkSecurityGroup': {'id': nsg}, 'ipConfigurations': [{'name': 'primary', 'properties': {
            'privateIPAllocationMethod': 'Dynamic',
            'subnet': {'id': "[resourceId('Microsoft.Network/virtualNetworks/subnets', 'audit-vnet', 'audit')]"},
            'publicIPAddress': {'id': pip, 'properties': {'deleteOption': 'Delete'}}}}]}, [nsg, vnet, pip])
    publisher, offer, sku, version = IMAGE.split(':')
    resource('Microsoft.Compute/virtualMachines', 'audit-vm', {
        'hardwareProfile': {'vmSize': state['vm_size']},
        'securityProfile': {'securityType': 'TrustedLaunch',
                            'uefiSettings': {'secureBootEnabled': True, 'vTpmEnabled': True}},
        'storageProfile': {'diskControllerType': 'NVMe',
            'imageReference': {'publisher': publisher, 'offer': offer, 'sku': sku, 'version': version},
            'osDisk': {'name': 'audit-os', 'createOption': 'FromImage', 'deleteOption': 'Delete',
                       'diskSizeGB': 64, 'managedDisk': {'storageAccountType': 'StandardSSD_LRS'}}},
        'osProfile': {'computerName': 'audit-vm', 'adminUsername': 'audituser',
            'customData': "[parameters('customData')]", 'linuxConfiguration': {
                'disablePasswordAuthentication': True, 'ssh': {'publicKeys': [{
                    'path': '/home/audituser/.ssh/authorized_keys', 'keyData': "[parameters('sshPublicKey')]"}]}}},
        'networkProfile': {'networkInterfaces': [{'id': nic, 'properties': {'deleteOption': 'Delete'}}]}},
        [nic], api='2024-07-01')
    return {'$schema': 'https://schema.management.azure.com/schemas/2019-04-01/deploymentTemplate.json#',
            'contentVersion': '1.0.0.0', 'parameters': {
                'customData': {'type': 'secureString'}, 'sshPublicKey': {'type': 'string'}},
            'resources': resources}
